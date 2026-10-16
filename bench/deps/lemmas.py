import re, sys, json, pathlib

HEAD = re.compile(r'^[ \t]*(?:Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example)\s+([A-Za-z_][\w\']*)', re.M)
PROOF, END = re.compile(r'\bProof\.'), re.compile(r'\b(Qed|Defined|Admitted)\.')

def project_files(root):
    return [l.strip() for l in (root/'_CoqProject').read_text().splitlines() if l.strip().endswith('.v')]

def locate(text, name):
    m = re.search(rf'^[ \t]*(?:Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example)\s+{re.escape(name)}\b', text, re.M)
    p = PROOF.search(text, m.end()); e = END.search(text, p.end())
    return m.start(), p.end(), e.start(), e.end()

def scan(root):
    out = []
    for f in project_files(root):
        s = (root/f).read_text()
        for m in HEAD.finditer(s):
            p = PROOF.search(s, m.end()); e = END.search(s, p.end())
            out.append(dict(file=f, line=s.count('\n', 0, m.start()) + 1, name=m.group(1),
                            ending=e.group(1), proof=s[p.end():e.start()].strip()))
    return out

if __name__ == "__main__":
    json.dump(scan(pathlib.Path(sys.argv[1])), sys.stdout, indent=1)
