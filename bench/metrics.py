import re
from collections import Counter
from urllib.parse import urlparse

URL = re.compile(r'https?://[^\s"\'<>\])},]+')
PROJECT = re.compile(r'oak_coq|sank20144|bitmap.allocator.in.rocq', re.I)
STATUS = re.compile(r'STATUS:\s*(PROVED|FAILED|UNPROVABLE)')
ERROR_KINDS = [
    ("incomplete proof", r"incomplete proof|Attempt to save|given up|No more (sub)?goals|not fully proved|unfocused|remaining goals?"),
    ("unification", r"Unable to unify|[Cc]annot unify|Impossible to unify"),
    ("type mismatch", r"has type.*expected to have type|is expected to have type|Illegal application"),
    ("not found", r"was not found|Unbound|No such|not a defined object|Cannot find"),
    ("syntax", r"Syntax error|Lexer|Illegal begin|Invalid notation"),
    ("tactic failure", r"Tactic failure|No applicable tactic|lia failed|Cannot (prove|find)|failed|No matching clauses|not an inductive"),
    ("timeout", r"Timeout|timed out"),
]


def flatten(content):
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        return "\n".join(c.get("text", "") if isinstance(c, dict) else str(c) for c in content)
    return "" if content is None else str(content)


def host_blocked(url, blocked):
    host = (urlparse(url).hostname or "").lower()
    return any(b.search(host) for b in blocked)


def rocq_errors(text):
    out = []
    for m in re.finditer(r'Error:\s*(.+?)(?:\n\s*\n|\Z)', text, re.S):
        msg = " ".join(m.group(1).split())[:400]
        kind = next((k for k, rx in ERROR_KINDS if re.search(rx, msg)), "other")
        out.append((kind, msg))
    return out


def attempt_metrics(events, rocq_runs, proxy_lines, blocked, target_file, t0):
    calls, by_id, usage, texts = [], {}, {}, []
    init = result = api_error = None
    for ev in events:
        t, e = ev["t"], ev["e"]
        kind, sub = e.get("type"), e.get("parent_tool_use_id") is not None
        if kind == "system" and e.get("subtype") == "init":
            init = e
        elif kind == "assistant":
            m = e.get("message", {})
            if e.get("error") or e.get("is_api_error_message"):
                api_error = f'{e.get("error") or "api error"}: {flatten(m.get("content"))[:300]}'
            usage[m.get("id")] = (m.get("usage") or {}, sub)
            for b in m.get("content", []):
                if b.get("type") == "tool_use":
                    c = dict(t=round(t - t0, 2), id=b["id"], name=b["name"], input=b.get("input", {}), sub=sub,
                             is_error=None, result="")
                    calls.append(c)
                    by_id[b["id"]] = c
                elif b.get("type") == "text" and not sub:
                    texts.append(b["text"])
        elif kind == "user":
            content = e.get("message", {}).get("content", [])
            for b in content if isinstance(content, list) else []:
                c = by_id.get(b.get("tool_use_id")) if isinstance(b, dict) else None
                if c is not None and b.get("type") == "tool_result":
                    c.update(is_error=bool(b.get("is_error")), result=flatten(b.get("content")), t_end=round(t - t0, 2))
        elif kind == "result":
            result = e
            if e.get("terminal_reason") == "api_error" and not api_error:
                api_error = f'api error: {str(e.get("result"))[:300]}'

    tokens = Counter()
    for u, _ in usage.values():
        for k in ("input_tokens", "output_tokens", "cache_creation_input_tokens", "cache_read_input_tokens"):
            tokens[k] += u.get(k) or 0
    main_turns = sum(1 for _, sub in usage.values() if not sub)

    errors = [(c["t"], k, msg) for c in calls for k, msg in rocq_errors(c["result"])]
    compiles = [r for r in rocq_runs if any(a.endswith(".v") for a in r["args"])]
    target = [r for r in compiles if any(a.endswith(target_file) for a in r["args"])]
    first_ok = next((i + 1 for i, r in enumerate(target) if r["exit"] == 0), None)

    searches, fetched, web_flags = [], [], []
    for c in calls:
        inp = c["input"]
        if c["name"] == "WebSearch":
            urls = URL.findall(c["result"])
            searches.append(dict(t=c["t"], query=inp.get("query", ""), urls=urls))
            web_flags += [f"search result from a blocked site: {u}" for u in urls if host_blocked(u, blocked)]
            if PROJECT.search(inp.get("query", "")):
                web_flags.append(f"search mentions this project: {inp.get('query')}")
        elif c["name"] == "WebFetch":
            fetched.append(dict(t=c["t"], url=inp.get("url", ""), error=c["is_error"]))
        elif c["name"] == "Bash":
            fetched += [dict(t=c["t"], url=u, via="bash") for u in URL.findall(inp.get("command", ""))]
    for f in fetched:
        if host_blocked(f["url"], blocked):
            web_flags.append(f"tried to open a blocked site: {f['url']}")
        if PROJECT.search(f["url"]):
            web_flags.append(f"opened a URL that mentions this project: {f['url']}")

    hosts, refused = Counter(), Counter()
    for line in proxy_lines:
        m = re.search(r'Request \(file descriptor \d+\): (?:CONNECT|GET|POST|HEAD|PUT|DELETE|OPTIONS)\s+(\S+)', line)
        if m:
            target_url = m.group(1)
            hosts[urlparse(target_url if "://" in target_url else "//" + target_url).hostname or target_url] += 1
        m = re.search(r'refused on filtered domain "([^"]+)"', line)
        if m:
            refused[m.group(1)] += 1
    web_flags += [f"the proxy refused {h} ({n}x)" for h, n in refused.items()]

    final = (result or {}).get("result") or (texts[-1] if texts else "")
    report = STATUS.findall(final)
    return dict(
        api_error=api_error, model=(init or {}).get("model"), claude_code_version=(init or {}).get("claude_code_version"),
        mcp_servers=(init or {}).get("mcp_servers"), finished_normally=result is not None,
        result_subtype=(result or {}).get("subtype"),
        turns=(result or {}).get("num_turns") or main_turns, cost_usd=(result or {}).get("total_cost_usd"),
        tokens=dict(tokens), tool_calls=len(calls), tool_counts=dict(Counter(c["name"] for c in calls)),
        tool_errors=sum(1 for c in calls if c["is_error"]), subagent_calls=sum(1 for c in calls if c["sub"]),
        rocq_runs=len(compiles), rocq_failed=sum(1 for r in compiles if r["exit"]),
        coqtop_runs=sum(1 for r in rocq_runs if r["tool"] == "coqtop"),
        target_checks=len(target), target_checks_until_success=first_ok,
        mcp_calls=sum(1 for c in calls if c["name"].startswith("mcp__")),
        errors=len(errors), error_kinds=dict(Counter(k for _, k, _ in errors)),
        error_samples=[dict(t=t, kind=k, message=m) for t, k, m in errors[:40]],
        searches=searches, fetched=fetched, proxy_hosts=dict(hosts), web_flags=sorted(set(web_flags)),
        self_report=report[-1] if report else None, final_message=final[-3000:],
        timeline=[dict(t=c["t"], t_end=c.get("t_end"), name=c["name"], sub=c["sub"], error=c["is_error"],
                       input=str(c["input"])[:1500], result=c["result"][:1500]) for c in calls],
    )
