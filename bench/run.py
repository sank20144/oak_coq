#!/usr/bin/env python3
"""Runs the agent proof benchmark. The agent gets one lemma at a time, from the
top of the first file down, in a fresh Claude Code session inside the
oak-coq-agent container. After each attempt the checker decides whether the
lemma was proved. Everything the dashboard shows is written under
bench/runs/<run id>/.

  export CLAUDE_CODE_OAUTH_TOKEN=...      # from `claude setup-token`
  bench/run.py --model claude-opus-5-5 --tools cli
  bench/run.py --resume <run id>          # carry on after an interruption
"""
import argparse, difflib, functools, http.server, json, os, re, shutil, string, subprocess, sys, threading, time
from datetime import datetime, timezone
from pathlib import Path

BENCH = Path(__file__).resolve().parent
REPO, RUNS = BENCH.parent, BENCH / "runs"
sys.path.insert(0, str(BENCH / "deps"))
sys.path.insert(0, str(BENCH))
from lemmas import scan, project_files
from check import check, without_ending
from metrics import attempt_metrics

AGENT_IMAGE, PROXY_IMAGE, TOOLCHAIN_IMAGE = "oak-coq-agent", "oak-coq-proxy", "oak-coq-toolchain"
# rocq_verify rejects files with Admitted and there's only one opam switch
MCP_DISABLED = ["mcp__rocq__rocq_verify", "mcp__rocq__rocq_switch"]
MCP_PROMPT = """
You also have Rocq MCP tools (their names start with `mcp__rocq__`):
`rocq_start` opens a proof session at a theorem and shows its goals,
`rocq_check` and `rocq_step_multi` run or try tactics from a state,
`rocq_query` runs `Search`, `Check`, `Print` and `About`, `rocq_toc` lists a
file's contents and `rocq_compile_file` compiles a file. `rocq_compile_file`
deletes the file's compiled `.vo` afterwards unless you pass `keep_vo=true`,
so rebuild with `make` if a later import fails. Confirm with a full build
before you finish.
"""
NO_TOKEN = "set CLAUDE_CODE_OAUTH_TOKEN first (create one with `claude setup-token`)"
BLOCKED = [re.compile(l.strip()) for l in (BENCH / "proxy/blocked.txt").read_text().splitlines()
           if l.strip() and not l.startswith("#")]


class ApiError(Exception):
    pass


def sh(*cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def write_json(path, obj):
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(obj, indent=1))
    tmp.replace(path)


def read_files(ws):
    return {f: (ws / f).read_text() for f in ["_CoqProject", *project_files(ws)]}


def reset_workspace(ws, files):
    for p in sorted(ws.rglob("*"), reverse=True):
        if p.is_file() or p.is_symlink():
            p.unlink()
        elif p.is_dir():
            p.rmdir()
    for f, s in files.items():
        (ws / f).write_text(s)
    os.chmod(ws, 0o777)
    for f in files:
        os.chmod(ws / f, 0o666)


def disabled_tools(args):
    # WebSearch goes through Anthropic, not our proxy, so offline mode turns it off
    return (MCP_DISABLED if args.tools == "mcp" else []) + (["WebSearch", "WebFetch"] if args.internet == "none" else [])


def similarity(a, b):
    norm = lambda s: " ".join(s.split())
    return round(difflib.SequenceMatcher(None, norm(a), norm(b)).ratio(), 3) if a and b else None


class Run:
    def __init__(self, args):
        self.args = args
        if args.resume:
            self.dir = RUNS / args.resume
            self.meta = json.loads((self.dir / "meta.json").read_text())
            for k in ("model", "tools", "time_limit", "max_turns", "attempts", "fake", "fake_plan"):
                setattr(args, k, self.meta[k])
            args.internet = self.meta.get("internet", "filtered")
            args.effort = self.meta.get("effort")
            args.limit = args.limit or self.meta.get("limit", 0)
            if not args.fake and not os.environ.get("CLAUDE_CODE_OAUTH_TOKEN"):
                sys.exit(NO_TOKEN)
        else:
            stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
            short = "fake" if args.fake else re.sub(r"[^A-Za-z0-9_.-]+", "-", args.model.replace("claude-", ""))
            self.dir = RUNS / f"{stamp}-{short}-{args.tools}"
            self.dir.mkdir(parents=True)
            self.meta = dict(
                id=self.dir.name, model=args.model, tools=args.tools, time_limit=args.time_limit,
                max_turns=args.max_turns, attempts=args.attempts, fake=args.fake, fake_plan=args.fake_plan, limit=args.limit, internet=args.internet, effort=args.effort,
                git_commit=sh("git", "-C", str(REPO), "rev-parse", "HEAD").stdout.strip(),
                git_branch=sh("git", "-C", str(REPO), "rev-parse", "--abbrev-ref", "HEAD").stdout.strip(),
                claude_code_version=sh("docker", "run", "--rm", "--network", "none", AGENT_IMAGE,
                                       "claude", "--version").stdout.strip(),
                blocked_hosts=[b.pattern for b in BLOCKED], disabled_tools=disabled_tools(args),
                started=time.time())
            ws = self.dir / "workspace"
            ws.mkdir()
            theories = "oak_coq/theories"
            proj = sh("git", "-C", str(REPO), "show", f"HEAD:{theories}/_CoqProject").stdout
            files = {"_CoqProject": proj}
            for f in [l.strip() for l in proj.splitlines() if l.strip().endswith(".v")]:
                files[f] = sh("git", "-C", str(REPO), "show", f"HEAD:{theories}/{f}").stdout
            reset_workspace(ws, files)
            if not_admitted := [l["name"] for l in scan(ws) if l["ending"] != "Admitted"]:
                shutil.rmtree(self.dir)
                sys.exit(f"{self.dir.name}: the checked-out commit still has proofs ({', '.join(not_admitted[:3])}, ...); "
                         "run on the benchmark commit, where every proof is Admitted")
        self.ws = self.dir / "workspace"
        self.graph = {x["name"]: x for x in json.loads((BENCH / "deps/graph.json").read_text())}
        self.order = scan(self.ws)
        if self.args.limit:
            self.order = self.order[:self.args.limit]
        self.names = set(self.graph)
        self.meta.update(status="running", lemmas=len(self.order), resumed=self.meta.get("resumed", 0) + bool(args.resume))
        self.prompt = string.Template((BENCH / "prompt.md").read_text())
        self.net, self.proxy = f"oakbench-net-{self.dir.name}", f"oakbench-proxy-{self.dir.name}"
        self.agent = None
        self.save_meta()

    def save_meta(self):
        write_json(self.dir / "meta.json", self.meta)
        index_path = RUNS / "index.json"
        index = json.loads(index_path.read_text()) if index_path.exists() else []
        index = [r for r in index if r["id"] != self.meta["id"]]
        index.append({k: self.meta.get(k) for k in ("id", "model", "tools", "status", "started", "finished", "fake")}
                     | {"headline": self.meta.get("headline")})
        write_json(index_path, sorted(index, key=lambda r: r["started"]))

    def results(self):
        out = []
        for i, lem in enumerate(self.order):
            p = self.dir / "lemmas" / f"{i:03d}-{lem['name']}" / "result.json"
            if p.exists():
                out.append(json.loads(p.read_text()))
        return out

    def write_summary(self):
        rows = self.results()
        count = lambda s: sum(1 for r in rows if r["status"] == s)
        t, proved, cost, curve = 0.0, 0, 0.0, []
        for r in rows:
            t += r["seconds"]; cost += r.get("cost_usd") or 0
            proved += r["status"] in ("proved", "proved_flagged")
            curve.append(dict(i=r["index"], seconds=round(t, 1), cost=round(cost, 4), proved=proved))
        headline = dict(done=len(rows), total=len(self.order), proved=count("proved"),
                        proved_flagged=count("proved_flagged"), failed=count("failed"), rejected=count("rejected"),
                        seconds=round(t, 1), cost_usd=round(cost, 4))
        self.meta["headline"] = headline
        write_json(self.dir / "summary.json", dict(headline=headline, curve=curve, rows=rows))
        self.save_meta()

    def start_network(self):
        sh("docker", "rm", "-f", self.proxy)
        sh("docker", "network", "rm", self.net)
        for cmd in (["docker", "network", "create", "--internal", self.net],
                    ["docker", "run", "-d", "--name", self.proxy, PROXY_IMAGE,
                     *(["tinyproxy", "-d", "-c", "/etc/tinyproxy/offline.conf"] if self.args.internet == "none" else [])],
                    ["docker", "network", "connect", self.net, self.proxy]):
            r = sh(*cmd)
            if r.returncode:
                sys.exit(f"could not set up the network: {' '.join(cmd)}\n{r.stderr}")

    def stop_network(self):
        sh("docker", "rm", "-f", self.proxy)
        sh("docker", "network", "rm", self.net)

    def proxy_log(self, t0, t1):
        iso = lambda t: datetime.fromtimestamp(t, timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.%fZ")
        r = sh("docker", "logs", "--timestamps", "--since", iso(t0), "--until", iso(t1 + 1), self.proxy)
        return (r.stdout + r.stderr).splitlines()

    def attempt(self, idx, lem, n, adir):
        adir.mkdir(parents=True, exist_ok=True)
        logs = adir / "logs"
        logs.mkdir(exist_ok=True)
        os.chmod(logs, 0o777)
        ending = "Defined" if self.graph[lem["name"]]["ending"] == "Defined" else "Qed"
        prompt = self.prompt.substitute(lemma=lem["name"], file=lem["file"], line=lem["line"], ending=ending,
                                        minutes=round(self.args.time_limit / 60),
                                        tools=MCP_PROMPT if self.args.tools == "mcp" else "")
        (adir / "prompt.md").write_text(prompt)
        before = read_files(self.ws)
        name = f"oakbench-agent-{self.dir.name}-{idx:03d}-{n}"
        proxy_url = f"http://{self.proxy}:8888"
        cmd = ["docker", "run", "--rm", "--name", name, "--network", self.net,
               "-e", f"HTTPS_PROXY={proxy_url}", "-e", f"HTTP_PROXY={proxy_url}",
               "-e", f"https_proxy={proxy_url}", "-e", f"http_proxy={proxy_url}", "-e", "NO_PROXY=localhost,127.0.0.1",
               "-e", "CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC=1",
               "-v", f"{self.ws}:/home/coq/work", "-v", f"{logs}:/logs"]
        if self.args.fake:
            (adir / "fake_proof.txt").write_text(self.graph[lem["name"]]["proof"])
            mode = self.args.fake_plan.get(lem["name"], "prove")
            cmd += ["-e", f"FAKE_MODE={mode}", "-e", f"FAKE_LEMMA={lem['name']}", "-e", f"FAKE_FILE={lem['file']}",
                    "-e", f"FAKE_ENDING={ending}", "-v", f"{BENCH / 'test/fake_agent.py'}:/fake/fake_agent.py:ro",
                    "-v", f"{adir / 'fake_proof.txt'}:/fake/proof.txt:ro", AGENT_IMAGE, "python3", "/fake/fake_agent.py"]
        else:
            cmd += ["-e", "CLAUDE_CODE_OAUTH_TOKEN", AGENT_IMAGE, "claude", "-p", prompt, "--model", self.args.model,
                    "--output-format", "stream-json", "--verbose", "--dangerously-skip-permissions"]
            if self.args.max_turns:
                cmd += ["--max-turns", str(self.args.max_turns)]
            if self.args.effort:
                cmd += ["--effort", self.args.effort]
            cmd += ["--strict-mcp-config"]
            if self.args.tools == "mcp":
                cmd += ["--mcp-config", "/home/coq/mcp.json"]
            if off := disabled_tools(self.args):
                cmd += ["--disallowedTools", *off]

        events, t0 = [], time.time()
        live = dict(run=self.dir.name, index=idx, lemma=lem["name"], file=lem["file"], attempt=n,
                    started=t0, status="running", recent=[], tool_counts={})
        write_json(self.dir / "live.json", live)
        with open(adir / "events.jsonl", "w") as ev_file, open(adir / "stderr.log", "w") as err_file:
            self.agent = name
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=err_file, text=True)

            def reader():
                last = 0.0
                for line in proc.stdout:
                    t = time.time()
                    try:
                        e = json.loads(line)
                    except ValueError:
                        e = {"type": "raw", "text": line.rstrip()}
                    events.append(dict(t=t, e=e))
                    ev_file.write(json.dumps(dict(t=t, e=e)) + "\n")
                    ev_file.flush()
                    for b in (e.get("message") or {}).get("content", []) if isinstance(e.get("message"), dict) else []:
                        if isinstance(b, dict) and b.get("type") in ("tool_use", "text"):
                            label = b.get("name") or "text"
                            if b.get("type") == "tool_use":
                                live["tool_counts"][label] = live["tool_counts"].get(label, 0) + 1
                            snippet = json.dumps(b.get("input"))[:300] if b.get("type") == "tool_use" else b.get("text", "")[:300]
                            live["recent"] = (live["recent"] + [dict(t=round(t - t0, 1), kind=label, text=snippet)])[-25:]
                    if t - last > 1:
                        live["now"] = t
                        write_json(self.dir / "live.json", live)
                        last = t

            th = threading.Thread(target=reader, daemon=True)
            th.start()
            timed_out = False
            try:
                proc.wait(timeout=self.args.time_limit)
            except subprocess.TimeoutExpired:
                timed_out = True
                sh("docker", "kill", name)
                proc.wait()
            th.join(timeout=30)
            self.agent = None
        t1 = time.time()

        rocq_runs = []
        if (logs / "rocq.jsonl").exists():
            rocq_runs = [json.loads(l) for l in (logs / "rocq.jsonl").read_text().splitlines() if l.strip()]
        proxy_lines = self.proxy_log(t0, t1)
        (adir / "proxy.log").write_text("\n".join(proxy_lines))
        m = attempt_metrics(events, rocq_runs, proxy_lines, BLOCKED, lem["file"], t0)
        if m["api_error"]:
            # not the agent's fault, undo and stop so resuming retries this lemma
            reset_workspace(self.ws, before)
            raise ApiError(m["api_error"])
        after = read_files(self.ws)
        c = check(before, after, lem["name"], lem["file"], ending, self.names)
        reset_workspace(self.ws, after if c["status"] == "proved" else before)
        if timed_out and c["status"] == "failed" and not c["reason"].startswith("the files"):
            c["reason"] = f"stopped at the {self.args.time_limit} s time limit; " + c["reason"]
        res = dict(attempt=n, seconds=round(t1 - t0, 1), timed_out=timed_out, exit_code=proc.returncode,
                   check=c, **m)
        write_json(adir / "result.json", res)
        live.update(status="between attempts", now=time.time())
        write_json(self.dir / "live.json", live)
        return res

    def lemma(self, idx, lem):
        ldir = self.dir / "lemmas" / f"{idx:03d}-{lem['name']}"
        g = self.graph[lem["name"]]
        tries = []
        for n in range(1, self.args.attempts + 1):
            r = self.attempt(idx, lem, n, ldir / f"attempt-{n}")
            tries.append(r)
            if r["check"]["status"] == "proved":
                break
        last = tries[-1]
        c = last["check"]
        status = c["status"]
        if status == "proved" and c["relies_on_admitted"]:
            status = "proved_flagged"
        flags = [f for t in tries for f in t["web_flags"]]
        if c["relies_on_admitted"]:
            flags.append("relies on admitted: " + ", ".join(c["relies_on_admitted"]))
        if c["extra_axioms"]:
            flags.append("extra axioms: " + ", ".join(c["extra_axioms"]))
        claimed = last["self_report"]
        if claimed and (claimed == "PROVED") != (status in ("proved", "proved_flagged")):
            flags.append(f"agent reported {claimed} but the checker says {status}")
        sum_over = lambda k: sum((t.get(k) or 0) for t in tries)
        res = dict(
            index=idx, name=lem["name"], file=lem["file"], level=g["level"], original_deps=g["deps"],
            status=status, reason=c["reason"], attempts=len(tries), seconds=round(sum_over("seconds"), 1),
            timed_out=any(t["timed_out"] for t in tries), turns=sum_over("turns"),
            cost_usd=round(sum_over("cost_usd"), 4) if any(t.get("cost_usd") is not None for t in tries) else None,
            tokens={k: sum(t["tokens"].get(k, 0) for t in tries) for k in
                    ("input_tokens", "output_tokens", "cache_creation_input_tokens", "cache_read_input_tokens")},
            tool_calls=sum_over("tool_calls"), tool_errors=sum_over("tool_errors"),
            tool_counts={k: sum(t["tool_counts"].get(k, 0) for t in tries) for k in
                         sorted({k for t in tries for k in t["tool_counts"]})},
            rocq_runs=sum_over("rocq_runs"), rocq_failed=sum_over("rocq_failed"), coqtop_runs=sum_over("coqtop_runs"),
            mcp_calls=sum_over("mcp_calls"), target_checks=sum_over("target_checks"),
            target_checks_until_success=last["target_checks_until_success"] if status.startswith("proved") else None,
            errors=sum_over("errors"),
            error_kinds={k: sum(t["error_kinds"].get(k, 0) for t in tries) for k in
                         sorted({k for t in tries for k in t["error_kinds"]})},
            subagent_calls=sum_over("subagent_calls"), searches=sum(len(t["searches"]) for t in tries),
            fetches=sum(len(t["fetched"]) for t in tries), flags=sorted(set(flags)), self_report=claimed,
            relies_on_admitted=c["relies_on_admitted"], extra_axioms=c["extra_axioms"], deps_used=c["deps_used"],
            proof_lines=c.get("proof_lines"), proof_sentences=c.get("proof_sentences"),
            original_proof_lines=sum(1 for l in g["proof"].splitlines() if l.strip()),
            similarity_to_original=similarity(without_ending(c.get("proof") or ""), g["proof"]) if status.startswith("proved") else None,
        )
        write_json(ldir / "result.json", res)
        return res

    def go(self):
        done = {r["name"] for r in self.results()}
        self.start_network()
        try:
            for idx, lem in enumerate(self.order):
                if lem["name"] in done:
                    continue
                r = self.lemma(idx, lem)
                self.write_summary()
                print(f"[{idx + 1}/{len(self.order)}] {lem['name']}: {r['status']} {r['reason']}".rstrip(), flush=True)
            self.meta.update(status="finished", finished=time.time())
        except KeyboardInterrupt:
            if self.agent:
                sh("docker", "kill", self.agent)
            self.meta.update(status="interrupted", finished=time.time())
            print(f"\ninterrupted; carry on with: bench/run.py --resume {self.dir.name}")
        except ApiError as e:
            self.meta.update(status="stopped: " + str(e)[:200], finished=time.time())
            print(f"\nstopped because Claude Code reported {e}\ncarry on later with: bench/run.py --resume {self.dir.name}")
        finally:
            self.stop_network()
            self.write_summary()
            live = json.loads((self.dir / "live.json").read_text()) if (self.dir / "live.json").exists() else {}
            write_json(self.dir / "live.json", {**live, "status": self.meta["status"], "now": time.time()})


class QuietHandler(http.server.SimpleHTTPRequestHandler):
    def log_message(self, *args):
        pass


def serve_dashboard(port=8000):
    try:
        srv = http.server.ThreadingHTTPServer(("127.0.0.1", port), functools.partial(QuietHandler, directory=str(BENCH)))
    except OSError as e:
        print(f"dashboard server not started ({e})", file=sys.stderr)
        return
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    print(f"dashboard: http://127.0.0.1:{port}/dashboard/", flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--model", default="claude-opus-5-5", help="e.g. claude-opus-5-5, claude-sonnet-5-5, claude-haiku-5-5")
    ap.add_argument("--tools", choices=["cli", "mcp"], default="cli",
                    help="cli: coqc/coqtop only; mcp: also the rocq-mcp server")
    ap.add_argument("--effort", choices=["low", "medium", "high", "xhigh", "max"],
                    help="the model's effort level (default: Claude Code's own default)")
    ap.add_argument("--internet", choices=["filtered", "none"], default="filtered",
                    help="filtered: the web minus the blocked sites; none: only Claude Code's own API")
    ap.add_argument("--time-limit", type=int, default=1800, help="seconds per attempt (default 1800)")
    ap.add_argument("--max-turns", type=int, default=0, help="turn limit per attempt (default: none)")
    ap.add_argument("--attempts", type=int, default=1, help="attempts per lemma, i.e. the k in pass@k (default 1)")
    ap.add_argument("--limit", type=int, default=0, help="only the first N lemmas (for trying things out)")
    ap.add_argument("--resume", metavar="RUN_ID", help="carry on with an interrupted run")
    ap.add_argument("--fake", action="store_true", help="use the fake agent (tests the harness, no model calls)")
    ap.add_argument("--fake-plan", type=json.loads, default={},
                    help='JSON mapping lemma -> prove|fail|wrong|violate|sleep for the fake agent')
    args = ap.parse_args()
    if not (args.fake or args.resume) and not os.environ.get("CLAUDE_CODE_OAUTH_TOKEN"):
        sys.exit(NO_TOKEN)
    for img in (AGENT_IMAGE, PROXY_IMAGE, TOOLCHAIN_IMAGE):
        if sh("docker", "image", "inspect", img).returncode:
            sys.exit(f"missing docker image {img}; see bench/README.md")
    serve_dashboard()
    Run(args).go()


if __name__ == "__main__":
    main()
