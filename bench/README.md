# Agent proof benchmark

This branch measures whether an AI agent can redo the proofs of the bitmap
allocator development, and records everything it does along the way.

On this branch the lemmas in `oak_coq/theories` are sorted by dependency level,
and every proof is replaced with `Admitted.`. The agent gets the lemmas one at a
time, from the top of the first file down, and may only write the proof. Each
lemma gets a fresh Claude Code session in a container that sees nothing but the
admitted `.v` files.

## How a run works

1. `run.py` copies the admitted files from the current commit into
   `runs/<run id>/workspace`. That copy is all the agent sees. It has no git
   history, no compiled files, and none of the original proofs.
2. For each lemma it starts Claude Code in the `oak-coq-agent` container with
   the prompt in `prompt.md`. The container sits on an internal Docker network
   whose only way out is the `oak-coq-proxy` container. The proxy blocks the
   hosts in `proxy/blocked.txt` (GitHub, Zenodo, Software Heritage, archive.org
   and services that serve GitHub files) and logs every host the agent contacts.
   With `--internet none` it instead lets through only `api.anthropic.com`, which
   Claude Code needs to talk to the model.
3. When the agent finishes, or the time limit runs out, `check.py` decides the
   outcome.
   - **Rejected** means the agent changed anything outside that lemma's proof,
     ended the proof with the wrong word (`Qed`, or `Defined` for
     `PageSize_eq_dec`), used `admit`/`Admitted`/`Abort`/`give_up`, put any
     other command into the proof (for example closing it early and declaring
     a new axiom after it), or switched off a Rocq check.
   - **Failed** means the proof still ends in `Admitted` or doesn't build.
   - **Proved** means it builds in a fresh `oak-coq-toolchain` container with no
     network.
   - **Proved, but flagged** means it was proved, but `Print Assumptions` shows
     it relies on an earlier lemma that is still `Admitted`.

   Extra standard-library axioms are accepted, and the dashboard lists them.
4. A proved lemma keeps the agent's proof. Any other outcome puts back
   `Admitted.`, and the run moves on to the next lemma.

If Claude Code reports an API error, such as a usage limit or an expired token,
the run stops without recording that lemma. Continue it later with `--resume`.

## Setting up (once)

The agent images start from the artifact image on Zenodo
([10.5281/zenodo.21032565](https://doi.org/10.5281/zenodo.21032565)).

    docker load -i oak-coq-docker-image.tar.gz                                  # oak-coq:latest
    docker build -t oak-coq-toolchain -f bench/toolchain.Dockerfile bench       # Coq without the project
    docker build -t oak-coq-agent bench/agent                                   # + Claude Code, rocq-mcp, pet
    docker build -t oak-coq-proxy bench/proxy                                   # the network filter

Building `oak-coq-agent` takes about half an hour, because opam recompiles Coq
8.20.1 there (same version) to install coq-lsp. The checker never uses that
copy of Coq.

Claude Code logs in with your subscription through a long-lived token. Create
one with `claude setup-token` and keep it in your shell. It is passed into the
container as an environment variable and is never written to disk.

    export CLAUDE_CODE_OAUTH_TOKEN=...

## Running

    bench/run.py --model claude-opus-5-5 --tools cli
    bench/run.py --model claude-sonnet-5-5 --tools mcp --limit 5      # first 5 lemmas only
    bench/run.py --resume 20261016-130000-opus-5-5-cli                # after Ctrl-C or an API error

| Option | Default | Meaning |
|---|---|---|
| `--model` | `claude-opus-5-5` | Any model Claude Code accepts, e.g. `claude-sonnet-5-5`, `claude-haiku-5-5` |
| `--tools` | `cli` | `cli` gives the agent coqc/coqtop only. `mcp` also gives it the rocq-mcp server |
| `--internet` | `filtered` | `filtered` allows the web except the blocked hosts. `none` lets the agent reach only Claude Code's own API (`proxy/allowed.txt`) and switches off its WebSearch and WebFetch tools |
| `--effort` | Claude Code's default | The model's effort level: `low`, `medium`, `high`, `xhigh` or `max` |
| `--time-limit` | `1800` | Seconds per attempt |
| `--max-turns` | none | Turn limit per attempt |
| `--attempts` | `1` | Attempts per lemma, each in a fresh session (pass@k) |
| `--limit` | all | Only the first N lemmas |

In `mcp` mode, two rocq-mcp tools are turned off because they cannot work here.
`rocq_verify` rejects any file that contains `Admitted`, and ours always do for
the later lemmas. `rocq_switch` changes opam switch, and the image has only one.

## Dashboard

`run.py` serves the dashboard while a run is going and prints its address,
http://127.0.0.1:8000/dashboard/. It refreshes every few seconds, so you can
watch the run live. To look at results when no run is going, serve it by hand.

    python3 -m http.server --bind 127.0.0.1 --directory bench 8000

- **All runs** lists every run, with a grid of lemma outcomes across runs.
- **Run page** shows the headline numbers and the live view. It has charts of
  lemmas proved over time and against cost, outcome by dependency level and by
  original proof length, time per lemma, tool calls by tool, Rocq errors by
  kind, and why lemmas failed. Below the charts is a sortable lemma table.
- **Lemma page** shows the agent's proof next to the original, the project
  lemmas each proof used, and every tool call on a timeline with its input and
  output. It also shows Rocq errors, web searches and their result URLs, the
  hosts the proxy saw, the agent's last message, the checker's output and the
  prompt.

Flags mark anything to look at. These include a search result or URL from a
blocked site, a query or URL that mentions this project, a host the proxy
refused, a proof that relies on admitted lemmas, extra axioms, and the agent's
own `STATUS:` line disagreeing with the checker.

Everything is also on disk in `runs/<run id>/`.

- `meta.json` holds the settings.
- `summary.json` holds the totals.
- `live.json` holds the current attempt.
- `lemmas/NNN-name/result.json` holds each lemma's outcome.
- `lemmas/NNN-name/attempt-N/` holds `events.jsonl` (the raw Claude Code
  stream), `prompt.md`, `logs/rocq.jsonl` (every coqc/coqtop run), `proxy.log`
  and `result.json`.

## Testing the harness without a model

`test/fake_agent.py` stands in for Claude Code. It prints the same kind of
events and really runs coqc and curl, and the plan says what it should do for
each lemma.

    bench/run.py --fake --limit 15 --time-limit 60 \
      --fake-plan '{"eq_length_repeat":"wrong","get_bit_bounds":"fail","set_bit_bounds":"violate","get_bit_set_bit_same":"sleep"}'

`python3 bench/test/test_check.py` checks the rule checks on their own. All
original proofs must pass them, and a list of tricks (edited statement, admit,
an axiom after `Qed`, and so on) must be rejected.

The modes are `prove` (writes the original proof, the default), `fail`,
`wrong`, `violate`, `sleep` and `apierror`. Test runs are hidden on the
dashboard unless you tick "Show test runs".

## The other files

- `deps/run.sh` works out which lemmas each proof uses and writes
  `deps/graph.json`. It has to run on files that still have the proofs. Level 0
  means a lemma uses no other project lemma, and a lemma's level is one more
  than the highest level among the lemmas it uses. The file also stores each
  original proof, for the dashboard's comparison.
- `deps/reorder.py deps/graph.json oak_coq/theories oak_coq/theories` sorts the
  lemmas in each file by level.
- `admit.py oak_coq/theories` replaces every proof with `Admitted.` and removes
  the comments saying which lemmas cannot be proven.
- `metrics.py` turns one attempt's logs into the numbers on the dashboard.
