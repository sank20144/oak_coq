import json, os, re, subprocess, time, uuid

MODE, LEMMA, FILE, ENDING = (os.environ[k] for k in ("FAKE_MODE", "FAKE_LEMMA", "FAKE_FILE", "FAKE_ENDING"))
WORK = "/home/coq/work"
turns = 0


def emit(obj):
    print(json.dumps(obj), flush=True)


def assistant(block):
    global turns
    turns += 1
    emit({"type": "assistant", "parent_tool_use_id": None, "message": {
        "id": "msg_" + uuid.uuid4().hex[:12], "content": [block],
        "usage": {"input_tokens": 1200, "output_tokens": 80, "cache_read_input_tokens": 9000,
                  "cache_creation_input_tokens": 300}}})


def tool(name, inp, run):
    tid = "toolu_" + uuid.uuid4().hex[:12]
    assistant({"type": "tool_use", "id": tid, "name": name, "input": inp})
    out, err = run()
    emit({"type": "user", "parent_tool_use_id": None, "message": {"content": [
        {"type": "tool_result", "tool_use_id": tid, "content": out, "is_error": err}]}})


def bash(cmd):
    def run():
        p = subprocess.run(["bash", "-c", cmd], capture_output=True, text=True, cwd=WORK)
        return (p.stdout + p.stderr)[-3000:], p.returncode != 0
    tool("Bash", {"command": cmd}, run)


def edit(transform):
    path = os.path.join(WORK, FILE)
    def run():
        text = open(path).read()
        open(path, "w").write(transform(text))
        return f"The file {path} has been updated.", False
    tool("Edit", {"file_path": path, "old_string": "Admitted.", "new_string": "..."}, run)


def set_proof(text, proof):
    m = re.search(rf'^[ \t]*(?:Lemma|Theorem)\s+{re.escape(LEMMA)}\b', text, re.M)
    p = text.index("Proof.", m.end()) + len("Proof.")
    e = text.index("Admitted.", p) + len("Admitted.")
    return text[:p] + "\n" + proof + text[e:]


emit({"type": "system", "subtype": "init", "model": "fake", "claude_code_version": "fake",
      "tools": ["Bash", "Edit", "WebSearch"], "mcp_servers": []})
assistant({"type": "text", "text": f"Let me look at {LEMMA} in {FILE}."})
build = "coq_makefile -f _CoqProject -o CoqMakefile >/dev/null && make -f CoqMakefile 2>&1 | tail -5"
bash(build)
tool("WebSearch", {"query": f"coq {LEMMA} proof"}, lambda: (
    'Links: [{"title":"a","url":"https://github.com/sank20144/oak_coq"},{"title":"b","url":"https://coq.inria.fr/doc"}]', False))
bash("curl -s -o /dev/null -w '%{http_code}' --max-time 10 https://example.com; echo; "
     "curl -s -o /dev/null -w '%{http_code}' --max-time 10 https://github.com || echo blocked")

if MODE == "apierror":
    emit({"type": "assistant", "parent_tool_use_id": None, "error": "rate_limit", "is_api_error_message": True,
          "message": {"id": "msg_err", "content": [{"type": "text", "text": "Claude AI usage limit reached"}], "usage": {}}})
    emit({"type": "result", "subtype": "success", "is_error": True, "terminal_reason": "api_error", "num_turns": 1,
          "total_cost_usd": 0, "result": "Claude AI usage limit reached", "usage": {}})
    raise SystemExit(1)
if MODE == "sleep":
    time.sleep(100000)
if MODE == "prove":
    edit(lambda t: set_proof(t, open("/fake/proof.txt").read().strip() + f"\n{ENDING}."))
elif MODE == "wrong":
    edit(lambda t: set_proof(t, "  exact I.\n" + f"{ENDING}."))
elif MODE == "violate":
    edit(lambda t: set_proof(t, open("/fake/proof.txt").read().strip() + f"\n{ENDING}.").replace(
        f"Lemma {LEMMA}", f"(* tweaked *)\nLemma {LEMMA}", 1))
if MODE != "fail":
    bash(build + f" && coqc -Q . OC.oak_coq.theories {FILE}")

status = {"prove": "PROVED", "wrong": "PROVED", "violate": "PROVED"}.get(MODE, "FAILED")
final = f"Done with {LEMMA}.\nSTATUS: {status}"
assistant({"type": "text", "text": final})
emit({"type": "result", "subtype": "success", "is_error": False, "num_turns": turns, "total_cost_usd": 0.01 * turns,
      "duration_ms": 1000, "result": final,
      "usage": {"input_tokens": 1200 * turns, "output_tokens": 80 * turns}})
