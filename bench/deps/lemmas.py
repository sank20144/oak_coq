import re, sys, json, pathlib
root = pathlib.Path(sys.argv[1])
files = [l.strip() for l in (root/'_CoqProject').read_text().splitlines() if l.strip().endswith('.v')]
head = re.compile(r'^\s*(Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example)\s+([A-Za-z_][A-Za-z0-9_\']*)')
end = re.compile(r'\b(Qed|Defined|Admitted)\.')
out = []
for f in files:
    lines = (root/f).read_text().splitlines()
    for i, l in enumerate(lines):
        m = head.match(l)
        if not m: continue
        for j in range(i, len(lines)):
            e = end.search(lines[j])
            if e: break
        out.append(dict(file=f, line=i+1, end_line=j+1, kind=m.group(1), name=m.group(2), ending=e.group(1)))
json.dump(out, sys.stdout, indent=1)
