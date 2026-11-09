# Definition Style

The form every chapter of the book follows. This is the one authority on
form: no stage restates these rules, and a chapter is judged against this file.
Rules are numbered so audits and comments can cite them (e.g. "breaks R5").
To see a rule in the exemplar, look it up in `exemplar-index.md`. The exemplar
shows the rules in use but is never an authority over them: where the two
differ, this file wins. Because every chapter is judged against this file and
nothing else, an agent that did not write a chapter can audit it fairly.

## Structure

- **S1 Phase by level grid.** The book is a grid of three phases (Syntax,
  Static Semantics, Dynamic Semantics) against the language's levels (for SML:
  Core, Modules, Programs). Each cell is one section. The topmost level may
  combine all three phases in one section when it is small.
- **S2 Section order.** Syntax for every level first, then static semantics
  level by level, then dynamic semantics level by level, then the top level.
- **S3 Levels build upward.** A level may use the syntax and semantic objects
  of the levels below it. A lower level never mentions a higher one.
- **S4 Static before dynamic.** Static semantics is complete before dynamic
  semantics begins. Dynamic chapters may assume a phrase has elaborated, and
  say so where it matters.
- **S5 Opening paragraph.** Each semantics section opens by naming the objects
  it introduces and the sentences it lets us infer. One paragraph, no history.
- **S6 Appendices.** Required: derived forms, full grammar, initial static
  basis, initial dynamic basis. Optional, decided per book: overloading or
  other special cases, implementation-dependent details, history of the
  language, changes since a previous edition.
- **S8 Implementation-dependent details.** Where implementations of the
  language legitimately differ (the range of integers, how characters are
  represented, floating point corner cases), the body of the definition
  states only what every implementation must satisfy, using an abstract
  parameter where needed. Each implementation's concrete choices go in an
  appendix, one section per parameter, one row per implementation.
- **S7 Numbering.** Sections are numbered within chapters. Figures are numbered
  consecutively through the whole book. Rules are numbered consecutively
  through the whole book, never restarting per chapter.

## Bare Language and Derived Forms

- **B1 Bare language only.** Semantic rules are given for the bare language
  only. Everything else is a derived form.
- **B2 The test for derived.** A construct is derived when its whole meaning,
  static and dynamic, is given by a local syntactic translation into other
  syntax. If the translation needs type information, fresh state, or a side
  condition beyond fresh identifiers, the construct is bare.
- **B3 Translation tables.** Derived forms are given as two-column tables,
  "Derived Form" and "Equivalent Form", one table per phrase class (Expressions,
  Patterns, Types, Bindings, Declarations, and so on), each a numbered figure.
- **B4 Well-founded.** Every equivalent form uses bare syntax or derived forms
  from earlier rows. No cycles.
- **B5 Fresh identifiers** introduced by a translation are stated as such
  beneath the table ("where vid is new").
- **B6 Full grammar.** An appendix collates bare and derived syntax into one
  grammar, marking which productions are derived.

## Syntax Chapters

- **G1 Lexis before grammar.** In order: reserved words; special constants;
  comments; identifiers; lexical analysis; infixed operators.
- **G2 Identifier classes table.** A figure listing each identifier class with
  its metavariable and a short description ("vid  VId  value identifiers"),
  then which classes may be long (qualified).
- **G3 Lexical analysis** states the rule for splitting text into items
  (longest match, how reserved words win) in a paragraph, not a grammar.
- **G4 Grammar figures.** BNF with `::=`. One alternative per line. A right
  column gives each alternative a short roman label ("application",
  "sequential"). Optional parts in single angle brackets. Iteration written
  with explicit side notes such as "(n >= 1)".
- **G5 Precedence and associativity** are stated in prose under the grammar
  ("the syntax of types binds more tightly than that of expressions"), not
  encoded by splitting nonterminals.
- **G6 Syntactic restrictions** follow the grammar as a bulleted list. Each is a
  decidable condition on syntax alone (no repeated identifier in a pattern, no
  binding of reserved names). Anything needing types belongs in the static
  semantics.
- **G7 Terminals** are typewriter (`let`, `=>`). Nonterminals are italic
  metavariables (exp, dec). Classes of phrases are roman capitalised (Exp, Dec).

## Semantic Objects

- **O1 Objects before rules.** Every semantics section defines its objects
  before its first rule, in this order: simple objects, compound objects,
  operations on them.
- **O2 Simple objects figure.** Rows of the form "metavariable in Class
  description", e.g. "alpha or tyvar in TyVar  type variables". Write "x or
  synvar" when a syntactic class is reused as a semantic one.
- **O3 Compound objects figure.** Each row defines a class as a set
  expression: products, disjoint unions, finite maps, finite sets, sequences,
  e.g. "sigma in TypeScheme = union over k of TyVar^k x Type".
- **O4 Shared notation is defined once.** Finite map notation, projection
  ("E of B"), injection, modification (+), and domain and range are defined in
  the first semantics section that needs them and reused everywhere after.
- **O5 Decorated metavariables.** A metavariable with primes or subscripts
  ranges over the same class as the undecorated one. State this once.
- **O6 Operations before use.** Substitution, instantiation, closure,
  realisation, enrichment, matching, and similar are defined in prose with
  displayed formulas before the first rule that uses them.
- **O7 Properties, not proofs.** State a property only when the rules depend on
  it to make sense ("the following precise result may easily be
  demonstrated"), as an indented display. No proofs.

## Inference Rules

- **R1 Sentence form first.** The rules section begins by giving the general
  sentence form (e.g. "A |- phrase => A'"), naming what A and A' range over,
  how it is pronounced ("phrase elaborates to A' in context A"), and that other
  hypotheses are side conditions.
- **R2 Rule groups.** One group per phrase class, in grammar order. The group
  heading is the class name in the plural ("Atomic Expressions") with the boxed
  judgment form for that class at the right margin.
- **R3 Coverage.** Every production of the bare grammar has a rule, or is
  covered by a rule through options.
- **R4 Numbers.** Each rule carries its number in parentheses at the right.
- **R5 Side conditions** sit among the premises as ordinary mathematical
  statements ("tynames tau is a subset of T of C"). They are never prose.
- **R6 Options.** Phrases in single angle brackets are first options; in double
  angle brackets, second options. In each instance of a rule the first options
  are all present or all absent, likewise the second. State this convention
  once, at R1, and use it to merge rules that differ only by an optional part.
- **R7 Syntax-directed** wherever possible: one rule per production. When two
  rules cover one production, a Comment says why.
- **R8 Only defined objects.** A rule mentions no object, operation or
  metavariable not defined in the objects section or an earlier section.
- **R9 Non-determinism is named.** Where a rule does not determine its result
  uniquely (a fresh name, an arbitrary type), a Comment says so.

## Dynamic Conventions

- **D1 Reduced syntax.** The dynamic semantics opens by listing what is erased
  from the syntax first (type ascriptions, type phrases) as bullets.
- **D2 Effect conventions stated once.** Any effect the language has (state,
  exceptions, I/O, control) gets one convention, stated once with its full
  form, then omitted from rules that do not touch it.
- **D3 State convention** (if the language has state). States are omitted from
  rules that neither read nor change them. The full form threads states left to
  right through the premises, so premise order is evaluation order.
- **D4 Exception convention** (if the language has exceptions). For each rule
  and each premise whose result is not already a packet, there is an implicit
  extra rule in which that premise yields a packet and the conclusion yields
  the same packet. State the full form once.
- **D5 Compound variables.** A variable such as v/p ranges over the union of
  the classes of v and p. Extend operations to the extra cases explicitly
  (e.g. "VE + FAIL = FAIL").

## Comments

- **C1 Placement.** After each rule group, an italic "Comments:" heading, then
  entries "(n) text" in ascending rule order.
- **C2 Only the non-obvious.** Comment on why a side condition exists, what is
  absent from a premise and its consequence, which rule handles an apparent
  gap, or the effect on a programmer. Skip rules with nothing to say.
- **C3 Never paraphrase.** A comment that only restates the rule in words is
  deleted.
- **C4 Concrete examples** in typewriter are welcome when they show a
  consequence ("thus `1:'a` will not elaborate").

## Initial Basis

- **I1 Minimal.** The initial basis gives only what the definition needs:
  predefined types, constructors, exceptions and the few basic values the
  rules refer to. A wider library is out of scope.
- **I2 Paired.** Every identifier in the initial static basis has an entry in
  the initial dynamic basis, and the reverse.
