import json, sys
from collections import Counter
lemmas, tok, out = sys.argv[1:]
L = json.load(open(lemmas))
names = {x["name"] for x in L}
deps = {n: sorted((set(open(f"{tok}/{n}.txt").read().split()) & names) - {n}) for n in names}
level = {}
def lv(n):
    if n not in level: level[n] = 1 + max((lv(p) for p in deps[n]), default=-1)
    return level[n]
G = [dict(name=x["name"], file=x["file"], ending=x["ending"], level=lv(x["name"]), deps=deps[x["name"]]) for x in L]
json.dump(G, open(out, "w"), indent=1)
print("lemmas per level:", sorted(Counter(level.values()).items()))
