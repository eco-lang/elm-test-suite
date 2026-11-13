A formal definition of the Elm language: its grammar, its static semantics (which programs are legal, and their types) and its dynamic semantics (what they do), as numbered inference rules in the manner of *The Definition of Standard ML*. Every rule has its own page and a permanent address, so that it can be cited, linked to and discussed.

<note class="sd-draft-note">

**Draft.** This edition is a draft for review. Many of its rulings are provisional, and rule numbers may change between editions; a rule's address, which uses its name, does not.

</note>

<slot name="actions"></slot>

<note class="sd-also">

Also with a page each: [{{restrictions}} restrictions](/standard/restrictions), [{{derivedForms}} derived forms](/standard/derived-forms), [{{basis}} entries of the initial basis](/standard/basis) and [{{figures}} figures](/standard/figures).

</note>

<note class="sd-also">

**Mechanised.** The static and dynamic semantics are encoded in the proof assistant Lean 4, one constructor per rule, with a type inference proved sound and principal and an evaluator proved sound and complete. Lean proves which of the suite's test programs are legal, and runs those that compile to prove their checks. See the [Lean proofs](/standard/proofs), each with a page of its own.

</note>

<note class="sd-also">

**Take part.** Each of those pages, and each chapter, has a Discussions section: start a discussion of the item on GitHub with its Discuss link, and the discussion is shown on the page. See [all the discussions](/standard/discussions), or the [Standard category]({{categoryUrl}}) of the repository's GitHub Discussions.

</note>
