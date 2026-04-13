# OAK Coq Model

A model of OAK kernel in Coq.

## Prerequisites

To build this project, you need:
- OPAM (OCaml Package Manager)
- Coq `8.20.1` (the last release before the Rocq rename)
- `coq-stdpp-bitvector` version `1.12.0`

## Setup Instructions

We recommend using OPAM to manage the OCaml and Coq environments.

1. **Install OPAM**  
   Follow the instructions at [opam.ocaml.org](https://opam.ocaml.org/doc/Install.html).

2. **Initialize OPAM and Create a Switch**  
   Create a new OPAM switch to isolate the dependencies for this project:
   ```bash
   opam init
   opam switch create coq-oak ocaml-base-compiler.4.14.2
   eval $(opam env --switch=coq-oak)
   ```

3. **Add Coq Repository**  
   ```bash
   opam repo add coq-released https://coq.inria.fr/opam/released
   opam update
   ```

4. **Install Coq and Dependencies**  
   Install the specific versions of Coq and `coq-stdpp-bitvector`:
   ```bash
   opam install coq.8.20.1 coq-stdpp-bitvector.1.12.0
   ```

## Building the Project

Navigate to the `oak_coq/theories` directory and build the project using Coq's makefile generator:

```bash
cd oak_coq/theories
coq_makefile -f _CoqProject -o Makefile
make -f Makefile
```


