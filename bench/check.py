import pathlib, re, subprocess, sys, tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent / "deps"))
from lemmas import locate

FORBIDDEN = re.compile(r'\b(admit|Admitted|Abort|give_up)\b')
# axioms the original proofs already rely on
BASELINE = re.compile(r'^(PrimInt63|Uint63)\.|(^|\.)bitarray_fits_uint63$')
# lines like "foo is assumed to be guarded" mean a check was turned off
UNSAFE = re.compile(r'^\S.* (is assumed to be|relies on) ', re.M)


def strip_comments(s):
    out, depth, i = [], 0, 0
    while i < len(s):
        if s.startswith("(*", i):
            depth, i = depth + 1, i + 2
        elif depth and s.startswith("*)", i):
            depth, i = depth - 1, i + 2
        else:
            if not depth:
                out.append(s[i])
            i += 1
    return "".join(out)


def without_ending(proof):
    return re.sub(r'\b(Qed|Defined|Admitted)\.\s*$', '', proof.rstrip()).rstrip()


def proof_stats(body):
    body = without_ending(body)
    code = strip_comments(body)
    return dict(proof_lines=sum(1 for l in body.splitlines() if l.strip()),
                proof_sentences=len(re.findall(r'\.(?=\s|$)', code)))


def check(before, after, lemma, file, ending, names, timeout=900):
    r = dict(status="failed", reason="", relies_on_admitted=[], extra_axioms=[], deps_used=[], proof=None)
    others = sorted(f for f in set(before) | set(after) if f != file and before.get(f) != after.get(f))
    if others:
        return {**r, "status": "rejected", "reason": "changed other files: " + ", ".join(others)}
    _, p, _, e = locate(before[file], lemma)
    prefix, suffix, a = before[file][:p], before[file][e:], after.get(file, "")
    if not (a.startswith(prefix) and a.endswith(suffix) and len(a) >= len(prefix) + len(suffix)):
        return {**r, "status": "rejected", "reason": f"changed {file} outside the proof of {lemma}"}
    body = a[len(prefix):len(a) - len(suffix)]
    r["proof"] = body.strip()
    r.update(proof_stats(body))
    code = strip_comments(body)
    end = re.search(r'\b(Qed|Defined|Admitted)\.\s*$', code)
    if not end:
        return {**r, "status": "rejected", "reason": f"the proof does not end with {ending}."}
    if end.group(1) == "Admitted":
        return {**r, "reason": "the proof still ends with Admitted"}
    if end.group(1) != ending:
        return {**r, "status": "rejected", "reason": f"the proof ends with {end.group(1)}. instead of {ending}."}
    bad = sorted(set(FORBIDDEN.findall(code)))
    if bad:
        return {**r, "status": "rejected", "reason": "the proof uses " + ", ".join(bad)}

    mod = file[:-2]
    query = (f"From OC Require Import {mod}.\nPrint Assumptions {lemma}.\n"
             f"Set Printing Depth 1000000.\nSet Printing Width 200.\nPrint {lemma}.\n")
    script = ('eval $(opam env); mkdir t && cp /src/* t/ && cd t && '
              'coq_makefile -f _CoqProject -o CoqMakefile >/dev/null && '
              'if ! make -f CoqMakefile "${TARGET}o" >/tmp/build.log 2>&1; then tail -c 6000 /tmp/build.log; echo "@@BUILD_FAILED@@"; exit 0; fi; '
              'coqc -Q . OC.oak_coq.theories zz_check.v 2>&1')
    with tempfile.TemporaryDirectory() as d:
        for f, s in {**before, file: a, "zz_check.v": query}.items():
            (pathlib.Path(d) / f).write_text(s)
        try:
            out = subprocess.run(["docker", "run", "--rm", "--network", "none", "-e", f"TARGET={file}",
                                  "-v", f"{d}:/src:ro", "oak-coq-toolchain", "bash", "-lc", script],
                                 capture_output=True, text=True, timeout=timeout).stdout
        except subprocess.TimeoutExpired:
            return {**r, "reason": f"the checker's build took longer than {timeout} s"}
    if "@@BUILD_FAILED@@" in out:
        return {**r, "reason": "the files do not build", "build_log": out.replace("@@BUILD_FAILED@@", "").strip()[-4000:]}
    head, _, printed = out.partition(f"\n{lemma} =")
    if "Axioms:" not in head and "Closed under the global context" not in head:
        return {**r, "reason": "could not read Print Assumptions", "build_log": out[-4000:]}
    if UNSAFE.search(head):
        return {**r, "status": "rejected", "reason": "the proof switches off a Rocq check", "build_log": head[-4000:]}
    axioms = re.findall(r"^([A-Za-z_][\w.']*) :", head.split("Axioms:", 1)[-1], re.M) if "Axioms:" in head else []
    short = lambda n: n.rsplit(".", 1)[-1]
    r["relies_on_admitted"] = sorted({short(n) for n in axioms if short(n) in names})
    r["extra_axioms"] = sorted(n for n in axioms if not BASELINE.search(n) and short(n) not in names)
    r["deps_used"] = sorted(set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", printed)) & names - {lemma})
    return {**r, "status": "proved", "reason": ""}
