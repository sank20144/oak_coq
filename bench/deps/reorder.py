import json, re, sys, pathlib
G, src, dst = json.load(open(sys.argv[1])), pathlib.Path(sys.argv[2]), pathlib.Path(sys.argv[3])
level = {x["name"]: x["level"] for x in G}
head = re.compile(r'^\s*(Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example)\s+([A-Za-z_][\w\']*)')
defn = re.compile(r'^\s*(Definition|Fixpoint)\s+([A-Za-z_][\w\']*)')
endp = re.compile(r'\b(Qed|Defined|Admitted)\.')

def items(lines):
    out, i = [], 0
    while i < len(lines):
        m, d = head.match(lines[i]), defn.match(lines[i])
        if m:
            j = next(k for k in range(i, len(lines)) if endp.search(lines[k]))
            out.append(("lemma", m.group(2), i, j)); i = j
        elif d:
            j = next(k for k in range(i, len(lines)) if re.search(r'\.\s*(\(\*.*\*\))?\s*$', lines[k]))
            out.append(("def", d.group(2), i, j)); i = j
        i += 1
    return out

for f in sorted({x["file"] for x in G}):
    lines = (src/f).read_text().splitlines(keepends=True)
    its = items(lines)
    lem = [k for k, it in enumerate(its) if it[0] == "lemma"]
    if not lem: continue
    its = its[lem[0]:lem[-1]+1]
    s = its[0][2]                        # take the doc comment along
    k = s                                # find where the comment above starts
    while k > 0 and lines[k-1].strip(): k -= 1
    if k < s and lines[k].lstrip().startswith("(*"): s = k
    prefix, suffix = lines[:s], lines[its[-1][3]+1:]
    chunks, prev = [], s
    for kind, name, a, b in its:
        chunks.append((kind, name, "".join(lines[prev:b+1]))); prev = b + 1
    lemmas = sorted((c for c in chunks if c[0] == "lemma"), key=lambda c: level[c[1]])
    defs = [c for c in chunks if c[0] == "def"]
    body = []
    for c in lemmas:
        for d in list(defs):
            if re.search(rf'\b{re.escape(d[1])}\b', c[2]):
                body += [x[2] for x in defs[:defs.index(d)+1]]; defs = defs[defs.index(d)+1:]
        body.append(c[2])
    body += [d[2] for d in defs]
    moved = [c[1] for c in lemmas] != [c[1] for c in chunks if c[0] == "lemma"]
    if not moved:
        print(f"{f:30} unchanged"); continue
    out = "".join(prefix) + "".join(b if b.startswith("\n") else "\n" + b for b in body) + "".join(suffix)
    (dst/f).write_text(out)
    print(f"{f:30} reordered  lemmas={len(lemmas)} defs={sum(c[0]=='def' for c in chunks)}")
