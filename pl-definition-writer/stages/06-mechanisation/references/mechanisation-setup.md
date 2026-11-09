# Mechanisation Setup

Install and check the tool chosen in `shared/run-config.md`. Only one is
needed. Commands are for Debian or Ubuntu; on macOS use Homebrew where shown.

## Ott

Ott checks grammar and rules written close to paper notation, and generates
LaTeX and prover definitions.

```
sudo apt install opam
opam init -y && eval $(opam env)
opam install -y ott
```

Verify: `ott -version` prints a version number.

## Lean 4

Lean is a proof assistant and programming language. Install through `elan`,
its version manager:

```
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

Verify: `lean --version` and `lake --version` both print versions. Create the
encoding project with `lake new <slug>-mech` inside `definition/mechanisation/`.

## Coq (Rocq)

A proof assistant with extraction to OCaml.

```
sudo apt install opam
opam init -y && eval $(opam env)
opam install -y coq
```

Verify: `coqc --version` prints a version number.

## PLT Redex

A Racket library for executable semantics and random testing.

```
sudo apt install racket        # or: brew install --cask racket
raco pkg install --auto redex
```

Verify: `racket -l racket/base -l redex -e '(displayln "ok")'` prints `ok`.

## How the Workspace Uses the Tool

Stage 06 writes the encoding to `definition/mechanisation/`
with a README giving the one command that builds and runs it. Nothing outside
that folder is installed or changed by the stage.
