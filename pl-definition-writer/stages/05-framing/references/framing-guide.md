# Framing Guide

What the preface, introduction and appendices contain. Structural rules for
the appendix set are in `shared/definition-style.md` "Structure" (S6).

## Preface

The one place for argument and motivation. Unnumbered (`\chapter*`), with a
table of contents entry. Four parts, each a few paragraphs:

1. **Why a formal definition.** What a precise definition gives implementers,
   programmers who reason about programs, and anyone who must agree on what a
   program means.
2. **The language.** Its character in a paragraph or two: what it is for,
   which features shape the definition. No tutorial.
3. **The method.** The world of meanings (semantic objects) and why they, not
   the syntax, carry the language's character. Then the keystone: a phrase is
   always evaluated against a background, giving a sentence of the form
   background, phrase, meaning (in the exemplar, B |- P => M), and the
   definition's purpose is exactly to decree which such sentences hold, by
   rules from constituent phrases to compound ones. Then the factoring into
   static and dynamic semantics.
4. **This edition.** If there is a previous edition, what kinds of change were
   made and where they are listed. Acknowledgements last. Signed with the
   authors' names and the date.

## Introduction

Numbered chapter 1. In order:

1. How an implementation of the language is naturally organised (the one
   place implementation analogy is allowed): a program as a sequence of
   top-level declarations, each modifying a basis.
2. The phases: parsing, elaboration, evaluation; the static and dynamic basis.
3. The levels, and the grid table mapping phase and level to sections.
4. Bare language and derived forms, and where each is treated.
5. The appendices, one sentence each.
6. Notational conventions used throughout (pointers to where finite maps,
   options and the like are defined, not the definitions themselves).

## Full Grammar Appendix

Collate, in order, every grammar figure from the syntax chapters with the
derived forms merged into their productions. Mark each derived alternative
(for example with a superscript dagger and a note). Keep the syntax chapters'
precedence notes and restrictions by reference ("Restrictions as in Section
2.9"), not by copying.

## Initial Basis Appendices

- **Static basis.** The predefined type names and their arities and equality
  attributes, the static environment (types, constructors, exceptions, values
  with their type schemes), as figures in the same object notation as the
  static chapters.
- **Dynamic basis.** The corresponding values, exception names and basic
  values, and the meaning of each basic value as a function on values, defined
  mathematically.
- Name the basis with a subscript 0 (B_0 = T_0, ..., E_0) or the registry's
  equivalent.

## Optional Appendices

- **Overloading or special cases.** Anything the core rules deliberately leave
  to a side mechanism (overloaded constants and identifiers, defaulting).
  Precise, in the same rule style, with its own rule numbers continuing the
  sequence.
- **Implementation-dependent details (S8).** One section per parameter the
  body leaves abstract: what the body requires of it, then a table of each
  known implementation's choice with its consequences for programs.
- **History.** Prose; the only appendix that may be discursive. Credit people
  and earlier languages by name with citations.
- **Changes.** One section per change from the previous edition: what changed,
  why in one paragraph, which sections and rules it touches.
