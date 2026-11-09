# Prose Style

How the words between the formulas read. The voice of a formal definition is
precise, impersonal where it describes the language and first person plural
where it describes the authors' choices ("we have adopted the following
convention"). Spelling follows `run-config.md`.

## Hard Constraints

A chapter that breaks any of these is not finished.

1. **No hedging about the language.** The definition decrees; it does not
   suggest. Never "usually", "typically", "should", "might" about what the
   language does. "Usually" is allowed only about what a metavariable ranges
   over ("A is usually a context").
2. **No undefined terms.** Every technical word is either defined earlier in
   the book, defined in the sentence where it first appears (in italics), or
   standard mathematics (set, map, sequence, union).
3. **No implementation talk.** No compilers, passes, data structures, memory
   layout or performance. The one exception is the introduction, which may
   explain the phases by analogy with how an implementation is organised.
4. **No pedagogy.** No exercises, no "let us", no "as the reader will
   recall", no motivating tutorials. Examples appear only inside Comments, and
   only to show a consequence.
5. **One name per thing.** Use the notation registry's name for every object
   and judgment. Never a synonym for variety.
6. **No em dashes.** Use a colon, a comma, parentheses, or two sentences.
7. **Formulas are sentences.** Displayed formulas are part of the sentence that
   introduces them and take its punctuation.

## Sentence Rules

**Define, do not describe.**
- Wrong: "Type schemes are kind of like types with some variables that can be
  instantiated in different ways."
- Right: "A type scheme sigma = forall alpha^(k).tau *generalises* a type
  tau', written sigma > tau', if tau' = tau{tau_i/alpha_i} for some tau_1 to
  tau_k."

**Say what follows, and stop.**
- Wrong: "Rule 11 is interesting because it means that raise can have
  basically any type, which is really useful in practice when you want to
  raise an exception in any context."
- Right: "(11) Note that tau does not occur in the premise; thus a raise
  expression has arbitrary type."

**Name the convention, then use it silently.**
- Wrong: repeating "where s and s' are the states before and after" in every
  rule group.
- Right: state the state convention once with its full form, then write
  "The convention for options is the same as for the Core static semantics."

**Keep the authors' voice for choices only.**
- Wrong: "We can see that the expression evaluates to a value."
- Right: "To reduce the number of rules, we have adopted the following
  convention."

## Pacing

- Opening paragraphs of a section: three to six sentences.
- Between figures and rule groups: at most one short paragraph unless an
  operation is being defined.
- Comments: one to four sentences each. A comment longer than six sentences
  means a definition is missing from the objects section.
- The preface is the only place for extended argument, history or motivation.

## Terminology

| Use | For | Not |
|-----|-----|-----|
| elaborate, elaboration | the static phase | type check, compile |
| evaluate, evaluation | the dynamic phase | run, execute, interpret |
| basis | the top-level background (static or dynamic) | environment (when the whole basis is meant) |
| phrase, phrase class | a piece of syntax, its syntactic category | node, AST |
| sentence | an assertion such as A \|- phrase => A' | judgement instance |
| side condition | a premise not of sentence form | constraint, guard |
| semantic object | any element of a semantic class | value (unless a value is meant) |
| derived form | syntax defined by translation | sugar, syntactic sugar |
| bare language | syntax with rules of its own | core language (Core is a level) |

## What the Voice Is Not

Not a tutorial, not a reference manual, not a commentary on design choices.
Design rationale belongs in a separate commentary, which this workspace does
not write.
