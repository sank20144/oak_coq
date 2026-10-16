# Agent proof benchmark

On this branch the lemmas in `oak_coq/theories` are sorted by dependency level
and every proof is replaced with `Admitted.`. An agent gets the lemmas one at a
time, from the top of the first file down, and may only write the proof.

- `toolchain.Dockerfile` builds `oak-coq-toolchain`, which has Coq 8.20.1 and
  stdpp-bitvector but none of the project files. It starts from the artifact
  image, so load that first with
  `docker load -i oak-coq-docker-image.tar.gz` (from
  [Zenodo](https://doi.org/10.5281/zenodo.21032565)), then run
  `docker build -t oak-coq-toolchain -f bench/toolchain.Dockerfile bench`.
- `deps/run.sh` works out which lemmas each proof uses and writes
  `deps/graph.json`. Level 0 means a lemma uses no other project lemma, and a
  lemma's level is one more than the highest level among the lemmas it uses.
  It has to run on a commit that still has the proofs.
- `deps/reorder.py deps/graph.json oak_coq/theories oak_coq/theories` sorts the
  lemmas in each file by level.
- `admit.py oak_coq/theories` replaces every proof with `Admitted.` and removes
  the comments saying which lemmas cannot be proven.
