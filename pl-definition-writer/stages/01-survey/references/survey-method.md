# Survey Method

How to read an implementation and its design notes for the semantic content a
definition needs. The survey describes the language; it does not design the
book.

## Locating the Semantics

Most implementations divide along the same lines as the definition's phases.
Find each part and record its paths in the survey's "Sources" section.

| Definition Needs | Look For |
|------------------|----------|
| Reserved words, identifiers, constants, comments | Lexer, tokeniser, scanner; keyword tables; number and string literal parsing |
| Grammar | Parser (hand-written or a grammar file such as .y, .mly, .g4, .lalrpop); the AST type definitions |
| Infix and precedence | Fixity tables, operator precedence parsing, fixity declarations handled by the parser or a resolver pass |
| Desugaring (candidate derived forms) | A pass that rewrites the AST before type checking; functions named desugar, expand, lower, elaborate-to-core |
| Static semantics | Type checker, elaborator, inference, unification, kind checking, scope resolution, module or signature checking |
| Dynamic semantics | Interpreter, evaluator, abstract machine; or, for a compiler, the runtime and the lowering of each construct |
| Initial basis | Prelude, built-in environment, primitive tables, standard library roots |
| Behaviour examples | Test suites, especially tests expected to fail type checking or to raise at runtime |

When an implementation is a compiler with no interpreter, read the lowering of
each construct together with the runtime; record the source-level behaviour,
not the generated code.

## Reading for Behaviour

For every construct, extract three things and cite where each comes from:

1. **Form.** The grammar production and any restrictions the parser enforces
   beyond the grammar (these become syntactic restrictions if they need no
   type information).
2. **Static checks.** What must hold for the construct to be accepted, and what
   it contributes (a type, a binding, an environment). Note every check that
   needs information not local to the construct, such as generated type names
   escaping a scope.
3. **Runtime behaviour.** What it evaluates to, what state it reads or
   changes, what it raises, and the order in which its parts are evaluated.

Evaluation order matters to the definition (premise order in dynamic rules).
Record it explicitly, even where it seems obvious.

## Recognising Derived Forms

A construct is a candidate derived form when the implementation rewrites it to
other syntax before type checking, or when the design notes describe it as
shorthand. Record the rewrite exactly. Stage 02 decides; the survey only
records what the implementation does and whether the rewrite needs type
information or fresh names.

## Ambiguities Worth Logging

Log an entry whenever any of these holds:

- The notes and the implementation disagree.
- The notes are silent and the implementation's behaviour looks accidental
  (an artefact of a data structure, a missing check, an unspecified order).
- The implementation has two code paths that behave differently for the same
  construct.
- A behaviour depends on the host language or platform (integer overflow,
  float formatting, string encoding).
- Tests and code disagree.

Do not log matters of taste. Log only questions whose answer changes a rule,
an object, a restriction or the basis.

## Using Tests

Run the implementation on small programs when the code is hard to read and
the toolchain is available. Record the program and the observed result in the
survey as evidence. Never modify the implementation.
