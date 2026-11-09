# Semantics Guide

How to produce a semantics chapter. What each part must contain is in
`shared/definition-style.md`; this file covers the working method.

## Objects

1. **List what the rules will need first.** Read the survey's static checks
   (or runtime behaviours) for every construct of the level and list every kind
   of thing a rule must mention: types, names, environments, values, states.
   That list, not the implementation's data structures, decides the objects.
2. **Separate simple from compound.** A simple object has no parts the rules
   look inside (names, addresses, basic values). Everything else is compound.
3. **Define compound objects by set constructions only:** product, disjoint
   union, finite map, finite set, finite sequence, and the classes already
   defined. Never "a record with fields". If a definition needs a recursive
   class, give it as the smallest set closed under the constructions and say
   so.
4. **Reuse before defining.** Objects defined in a lower level or in the static
   chapter of this level are used by name. Never redefine; extend with a
   sentence if a class grows ("We extend Val with ...").
5. **Name what is not in the implementation.** The definition often needs
   objects an implementation keeps implicit (the set T of generated type
   names, an exception name set in the state). Add them where the rules need
   them and note the survey construct that motivates each.

## Operations

- Define each operation in prose with a displayed formula: its arguments, its
  result, and the condition under which it is defined.
- Order operations so each uses only those above it.
- Where a static operation is partial (matching, unification of record
  types), say what happens when it is undefined: the rule simply does not
  apply.

## Rules

For each phrase class, in grammar order:

1. **Write the judgment box** from the registry's "Judgment Forms".
2. **One rule per production.** Start from the bare grammar figure. Write the
   conclusion first: the production, in context, yielding its result.
3. **Premises from the survey.** Each static check or runtime step for the
   construct becomes a premise or a side condition. A check on a subphrase is
   a premise about that subphrase; a check relating results is a side
   condition.
4. **Dynamic premise order is evaluation order.** Under the state convention,
   the left-to-right order of premises is the order the survey recorded.
   Check it against the survey's "Evaluation Order" column for every rule.
5. **Merge with options.** Where two rules differ only by an optional
   subphrase, write one rule with first options (R6). Do not merge rules whose
   premises differ in kind.
6. **Exceptional rules.** For dynamic chapters, write explicitly only the rules
   that create or handle a packet. Propagation comes from the exception
   convention. A failed match yields FAIL, not a packet, unless the language
   defines otherwise.
7. **Number as you go.** Continue from the last rule number in the checklist's
   Rules column for the previous chapter.

## Comments

After each group, read every rule and ask:

- Is there a side condition whose purpose is not obvious? Comment on why.
- Does a metavariable fail to appear in the premises, so the result is
  unconstrained? Say what that means for the programmer.
- Does a rule look as if it is missing a case? Say which rule or convention
  covers it.
- Does an ambiguity ruling explain the rule's shape? Say what the rule
  decrees, without naming the log.

Write nothing for a rule with nothing to say. A short code example in
typewriter is welcome when it shows a consequence.

## The Top Level

When the top level (e.g. Programs) combines all three phases in one chapter,
write its syntax, its static rule and its dynamic rule in that order in one
file, and state how the static and dynamic bases are updated together, and
what happens when elaboration fails part way through a program.

## When the Survey Is Not Enough

If a rule cannot be settled from the survey and rulings, add an ambiguity
entry to `definition/survey/ambiguity-log.md` with the next free number
and ask for a ruling at the next checkpoint. Never decide silently.
