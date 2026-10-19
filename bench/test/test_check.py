import json, pathlib, sys
bench = pathlib.Path(__file__).resolve().parents[1]
sys.path[:0] = [str(bench), str(bench / "deps")]
from check import check, commands, strip_comments, ENDINGS, DECLARATIONS
from lemmas import project_files

for g in json.loads((bench / "deps/graph.json").read_text()):
    cmds = commands(strip_comments(g["proof"]))
    assert not {*cmds} & (ENDINGS | DECLARATIONS), (g["name"], cmds)

root = bench.parent / "oak_coq/theories"
before = {f: (root / f).read_text() for f in ["_CoqProject", *project_files(root)]}
f, lem = "BitArrLemmas.v", "get_bit_bounds"
s = before[f]; i = s.index("Proof.", s.index(f"Lemma {lem}")) + 6; j = s.index("Admitted.", i) + 9
tricks = {
    "statement edited": {**before, f: s.replace(f"Lemma {lem}", f"Lemma {lem} ", 1)},
    "other file edited": {**before, "BitArr.v": before["BitArr.v"] + "\n"},
    "_CoqProject edited": {**before, "_CoqProject": before["_CoqProject"] + "\n"},
    "admit": {**before, f: s[:i] + "\n  admit.\nQed." + s[j:]},
    "wrong ending": {**before, f: s[:i] + "\n  auto.\nDefined." + s[j:]},
    "axiom after Qed": {**before, f: s[:i] + "\n  auto.\nQed.\nAxiom cheat : False.\nLemma pad : True.\nProof. exact I. Qed." + s[j:]},
    "axiom inside": {**before, f: s[:i] + "\n  Axiom cheat : False.\n  destruct cheat.\nQed." + s[j:]},
    "option inside": {**before, f: s[:i] + "\n  Local Unset Guard Checking.\n  auto.\nQed." + s[j:]},
}
for name, after in tricks.items():
    r = check(before, after, lem, f, "Qed", set())
    assert r["status"] == "rejected", (name, r)
    print(f"{name:20} rejected: {r['reason']}")
print("ok")
