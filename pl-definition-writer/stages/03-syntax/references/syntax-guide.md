# Syntax Guide

How to produce each part of a syntax chapter. What each part must contain is
in `shared/definition-style.md` "Syntax Chapters"; this file covers the
working method.

## Lexis

**Reserved words.** Take the list from the survey's "Reserved Words". Set it
as a displayed block of terminals in the order the exemplar uses: alphabetic
words first, then symbols. State that reserved words may not be used as
identifiers, unless a ruling says otherwise.

**Special constants.** One paragraph per kind (integer, real, character,
string, and so on). Define each lexically, in words and with a small regular
pattern where that is clearer. Escape sequences go in a figure if there are
more than four.

**Comments.** One paragraph: delimiters, nesting, and what happens to an
unmatched delimiter.

**Identifiers.** The identifier classes figure (G2), then which classes may be
qualified, then any overlap rules (an alphanumeric identifier may be a value or
a type constructor depending on context, and so on). Every class here must be a
row of the registry's "Syntactic Classes".

**Lexical analysis.** One paragraph stating how source text splits into items:
longest match, how reserved words win over identifiers, where spaces are
required.

**Infixed operators.** Fixity declarations, default fixities, precedence
levels, associativity, and how an infixed identifier is used in prefix
position. If fixity is resolved by a separate pass in the implementation,
still describe it here as part of the syntax.

## Grammar Figures

1. Group phrase classes as the exemplar does: one figure for expressions,
   matches, declarations and bindings; one for patterns; one for types; and so
   on. A figure should fit on one page.
2. Order alternatives within a production as the parser's precedence runs,
   loosest to tightest, so the figure reads as the precedence table.
3. Give every alternative a right-column label: a noun phrase in roman
   ("application", "local declaration"). Mark alternatives that exist only as
   derived forms with no entry; they belong to the appendix.
4. Use first options for optional subphrases and the "(n >= 1)" note for
   iteration. Do not invent EBNF operators.
5. Caption each figure "Grammar: <Classes>".

## Restrictions

Write each as one bullet, in the form "No <phrase> may <condition>", or "In
<phrase>, <condition>". Group restrictions by phrase class. Each must be
checkable by looking at the phrase alone.

## Derived Forms Tables

1. Take the plan's "Derived Forms" rows for one phrase class.
2. Order the rows so each equivalent form uses only bare syntax or rows above
   it.
3. Write each equivalent form in full bare syntax with registered macros.
4. Under the table, list fresh identifiers ("In the equivalent form for
   `while`, vid is a new value identifier").
5. One figure per phrase class, captioned "Derived forms of <Classes>".

## When the Survey Is Not Enough

If a production's exact shape cannot be settled from the survey and rulings,
stop and add a new ambiguity entry to `definition/survey/ambiguity-log.md`
with the next free number, then ask the human for a ruling at the next
checkpoint. Never decide silently.
