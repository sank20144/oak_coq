You are working on a Rocq (Coq 8.20.1) development in /home/coq/work. It
formalises a Rust bitmap frame allocator on top of a small model of Rust
ownership and borrowing. The files are listed in build order in `_CoqProject`
and use the logical path `OC.oak_coq.theories`.

## Task

Prove the lemma `$lemma` in `$file` (it starts on line $line). Its proof
currently reads

    Proof.
    Admitted.

Replace `Admitted.` with a complete proof that ends with `$ending`.

## Rules

1. Only write the proof. The only text you may change is what sits between
   `Proof.` and `Admitted.` of `$lemma`. Everything else in every `.v` file and
   in `_CoqProject` must stay exactly as it is, including the statement, other
   lemmas and proofs, definitions, notations, Ltac, imports, options and
   comments.
2. The proof must end with `$ending` and must not use `admit`, `Admitted`,
   `Abort` or `give_up`, or switch off any of Rocq's checks.
3. Do not add axioms, parameters or new top-level lemmas. If you need a helper
   fact, prove it inside the proof, for example with `assert`.
4. You may use any lemma, definition or tactic that is in scope at that point,
   including the project's own Ltac. Earlier lemmas are in scope, and some of
   them may still be `Admitted`. Later lemmas are not in scope.
5. You may use the internet for documentation and general knowledge, but do not
   look for this project's original proofs.
6. You have about $minutes minutes, after which the attempt is stopped.

## Checking your work

Build everything in order with

    coq_makefile -f _CoqProject -o CoqMakefile && make -f CoqMakefile

Once the files before `$file` are built, you can check it on its own with
`coqc -Q . OC.oak_coq.theories $file`. To see the goals, put `Show.` after a
tactic, or work interactively with `coqtop -Q . OC.oak_coq.theories`.
$tools
## How to work

- Read the statement and the definitions it uses first, and look at how the
  nearby lemmas are proved.
- Use `Search`, `Check`, `Print` and `About` to find lemmas you can use.
- Build after every change and read the error messages carefully.
- If an approach keeps failing, step back and try a different one rather than
  repeating it.

## Finishing

End your last message with exactly one of these lines.

- `STATUS: PROVED` if the file builds and `$lemma` has a complete proof ending
  with `$ending`.
- `STATUS: FAILED` if you could not finish the proof.
- `STATUS: UNPROVABLE` if you believe the statement is false as written. Give a
  concrete argument or counterexample above the status line.

If you did not finish, leave the proof as `Admitted.`.
