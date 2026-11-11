# Book Brief

| Field | Value |
|-------|-------|
| Title | A Standard Definition of Elm? |
| Slug | standard-elm-definition |
| Authors | Rupert Smith (provisional; confirm at the first checkpoint) |
| Year | 2026 |
| Edition | Draft version 0.4 |
| Language | Elm |
| Version | Elm 0.19.1, as implemented by eco 0.2.0 |
| Implementation | /home/rupert/sc/gitlab/eco-compiler (compiler front end in `compiler/src`, written in Elm; runtime and kernels in C++) |
| Design notes | `/home/rupert/sc/gitlab/eco-compiler/THEORY.md`; `design_docs/` (above all `elm-divergence.md`, `float-semantics.md`, `char-case-mapping.md`, and `theory/`) |
| Behaviour evidence | `test/elm/` first (the operational semantics the implementation enforces); then `test/elm-conformance/`, `test/eco-divergence/`, `test/elm-core/`, `test/elm-compile-errors/` |
| Scope | In: the whole surface language including `port` declarations; the platform's Cmd, Sub and Task; the initial basis (Basics arithmetic and comparison, and the core types the rules mention). Out: kernel (JavaScript or C++) implementation code, `effect module` declarations and user `infix` declarations (both restricted to core packages), GLSL shader blocks, and library packages beyond what the initial basis needs |
| Previous edition | none |

## Author Directions

1. **Form.** Follow closely the structure, format and style of *The Definition
   of Standard ML (Revised)*.
2. **No exceptions.** Elm has no exceptions and pursues a no-runtime-errors
   philosophy. The dynamic semantics has no exception packets and no exception
   convention.
3. **Total arithmetic: the wrong answer, not an error.** Pure maths operations
   cannot fail; where an operation has no mathematically correct result, the
   definition gives a defined (wrong) answer instead. Example: `3 // 0 == 0`.
4. **Basic maths in the definition.** The basic arithmetic and comparison
   operations are defined precisely in the definition itself, not left to a
   library.
5. **Row-polymorphic records.** Elm has extensible (row-polymorphic) records,
   which ML does not. The static semantics must define them: record types with
   a row variable, field access, field accessors, and record update.
6. **Simple modules.** Elm's module system is much simpler than ML's: a module
   exports only top-level definitions, by name. No signatures, functors or
   sharing.
7. **Otherwise as ML.** Apart from directions 2 to 6, the semantics is
   extremely close to ML's; follow the SML Definition's treatment wherever the
   languages agree.
8. **Implementation details in an appendix.** Elm on JavaScript has 53-bit
   integers; eco has 64-bit integers on the native CPU. eco's `Char` is a
   single Unicode code point; Elm's chars are really short Unicode strings.
   Keep these out of the body of the definition and confine them to an
   implementation-dependent details appendix (definition-style S8).
9. **Sources.** Use the eco implementation, its `design_docs/`, `THEORY.md`,
   and its tests to shape the definition. `test/elm/` is the main evidence for
   the operational semantics.
10. **Cmd, Sub and Task get their own section.** They are integral to the
    language even though they are defined as data types rather than built-in
    syntax. The definition gives them a section of their own.
11. **Ports are part of the definition.** `port` is a reserved word, so port
    declarations belong to the language. The key thing to document precisely
    is what can and cannot be sent over a port.
