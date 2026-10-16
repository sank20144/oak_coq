import re, sys, pathlib
root = pathlib.Path(sys.argv[1])
files = [l.strip() for l in (root/'_CoqProject').read_text().splitlines() if l.strip().endswith('.v')]
head = re.compile(r'^[ \t]*(Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example)\s', re.M)
proof, end = re.compile(r'\bProof\.'), re.compile(r'\b(Qed|Defined|Admitted)\.')
hints = [" (* This should be true but cannot be proven due to the bug in Rusts implementation *)"]
total = 0
for f in files:
    s = (root/f).read_text()
    for h in hints: s = s.replace(h, "")
    out, i = [], 0
    for m in head.finditer(s):
        if m.start() < i: continue
        p = proof.search(s, m.end()); e = end.search(s, p.end())
        out.append(s[i:p.end()] + "\nAdmitted."); i = e.end(); total += 1
    (root/f).write_text("".join(out) + s[i:])
print(f"admitted {total} lemmas")
