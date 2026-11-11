# Audit X (2026-11-10): Notation, Definitions Before Use, Numbering, Static/Dynamic Agreement, Seams

Scope: the working-tree changes to definition/tex (A27 revised, A94 to A97) checked hard; a lighter pass of A1, A2, A5 and A6 over the whole book. Read only; the book was built in the scratchpad (build-x/).

## Mechanical checks

- Build (latexmk, scratchpad copy): no errors, no undefined or multiply defined references, 3 overfull boxes (5.3pt, 4.5pt, 1.4pt), as before.
- Rules: 194 `\defnrule`, numbered 1 to 194 in the .aux, each once (S7). All `\ruleref` targets cited by the new text exist (r:s-atexp-scon, r:s-atexp-longvar, r:s-dec-group, r:s-valbind-var, r:sm-topdec-value, r:p-stat-main-program, r:p-stat-main-view, r:p-dyn-main).
- New labels `sec:static-core-principal`, `sec:appendix-implementation-numbers` follow the scheme. The removed `res:core-number-default` has no remaining reference in the book.
- Registry: every macro of notation.md is defined in macros.sty/defn.sty and used (except `\jnot`, already known). No em dash (U+2014 or `---`) in any .tex file.

## Findings

### F1 Blocker: static-core.tex:446-475 (A2, A6, O7)
"Instance" allows only a substitution S of type and row variables, but derivations for modules and programs choose their new type names freely: r:sm-datbind takes any `t \in \TyName^{(k)}`, r:sm-topdec-types only requires `t \notin T \of C`. The book itself says the result is determined "up to the choice of the type names in Ran TE that are not in T of C" (static-modules.tex:347-349) and that programs agree "with the type names that the modules generate renamed" (programs.tex:292). So for a module that declares a custom type, a derivation that picks another new name t' is not an instance of the one that picks t. No derivation is then principal, and the Property ("Every phrase, module or program that elaborates has a principal derivation ... differ only by a renaming of type and row variables", 471-475) is false. Chapter 5 judges its further restrictions "on the principal derivation for the module" (static-modules.tex:586-588), and Chapter 6 starts from "the principal derivation of the program" (dynamic-core.tex:54-55). Both are undefined for such programs.
Fix: for modules and programs, let an instance also rename the type names that the derivation generates (a bijection on type names not in `T \of B`). State uniqueness as "up to a renaming of type and row variables and of generated type names".

### F2 Blocker: static-core.tex:434-438, 462-475; programs.tex:210-218 (A6, A2, R5)
Take an unannotated `main = Platform.worker { init = \_ -> (0, Cmd.none), ... }`. Rule r:p-stat-main-program has derivations whose module derivation gives the flags (), Int, String, and so on. Chapter 9 itself says "a derivation that took the flags to be () would satisfy the rule". None of these derivations is an instance of another, so the program "elaborates" by the rules (static-core.tex:529-530: "A phrase elaborates to A' when some derivation of the sentence exists") and has no principal derivation. That contradicts the Property for programs. Chapter 9 then says the program "does not elaborate" because "The derivations for the modules of a program are their principal derivations". That condition is in prose, not in the rule (R5). It also contradicts 4.9's "Elaboration does not depend on the choice" (438).
Fix: make the condition part of program elaboration. For example, state with the sentence forms of Chapter 9 that each premise `B \vdash modm \Rightarrow B', E` of r:p-stat-module, r:p-stat-main-program and r:p-stat-main-view is inferred by a principal derivation. Then restrict the Property to phrases and modules, and define a program's principal derivation as the one made of its modules' principal derivations. In 438, say "Elaboration of a Core phrase does not depend on the choice".

### F3 Blocker: dynamic-core.tex:56-63 (A6, A27 clarification)
Defaulting exempts only variables "bound ... by a closure (rules r:s-dec-group and r:sm-topdec-value)" or "by the quantifier ∀U' of an annotated binding (rule r:s-valbind-var)". The parameters of type declarations are explicit variables too: r:sm-datbind adds U, and its Clos_C binds them; r:sm-typbind and r:sm-typbind-record add them to the context, and Λ binds them. So are the variables of port annotations (r:sm-topdec-portout and r:sm-topdec-portin: "U is new for ty", Clos_C τ). Nothing forbids a parameter named `number` (syntax-core.tex:198-200; no restriction in syntax-modules). With `type alias Vec number = { x : number, y : number }`, the node `C + {α} ⊢ number ⇒ α` (r:s-ty-tyvar) has α of class number, which neither listed binder binds. Substituting Float gives `⊢ number ⇒ Float`, which no rule derives. So "which remains a derivation for the program" (59-60) is false.
A related problem: the copy clause (75-77) covers "each declaration ... at the top level of a module, whose bindings have type schemes that quantify type variables of class number". Read literally, that includes `type Box number = Box number`, whose constructor scheme quantifies number.
Fix: exempt every variable that is explicit at some node (a member of `U \of C`) or quantified by any closure or type-function binder of the derivation. Restrict copying to value declarations.

### F4 Major: static-core.tex:438-441 vs 491-494 and 850-851 (A6)
438-441 says: "Elaboration does not depend on the choice, but evaluation does: ... and so do the further restrictions of Section 4.11". That is, the further restrictions depend on the derivation. 492-494 says: "The further restrictions of this chapter give the same answer in every derivation". 850-851 agrees with 492-494.
Fix: in 438-441, say instead that the further restrictions are stated in terms of the type of a match, so they need a derivation to be named, although (Section 4.11) every derivation gives the same answer.

### F5 Major: static-core.tex:450-457 (A2, O6)
- "one substitution S that respects classes and rows": "respects rows" is defined nowhere. Section 4.3 defines only "respects classes" and when a substitution is defined.
- S is used as an object applied to types and schemes ("S applied to the corresponding type", "Sσ"). The book defines substitution only as the notation τ{τ^(k)/tyrowvar^(k)}.
- "each type in the sentence" leaves out the U and T components of contexts.
Fix: define S as a finite map from variables to types, with S τ meaning τ{...}. Say that S maps row variables to record types and is defined (the condition of Section 4.3). Say how U (S maps the renamed explicit variables back) and T (see F1) correspond.

### F6 Minor: static-core.tex:432-504 (A2, R1)
Section 4.9 comes before the Inference Rules (4.10). It uses "derivation", "node" and "sentence", and forward rule references (r:s-atexp-scon, r:s-atexp-longvar, r:s-dec-group), before the rules section gives the sentence form (R1). Nothing in 4.10 uses 4.9. 4.8 already refers forward to r:s-dec-group, so that part has a precedent.
Fix: move 4.9 between 4.10 and 4.11. 4.11 and the chapter introduction already point to it by label.

### F7 Minor: static-core.tex:434, 464-469, 494-496, 500 (S3, S4)
The Core chapter does three things that belong to higher levels or to the dynamic semantics:
- It defines principal derivations "for a module or a program (Chapters 5 and 9) in a static basis" and states the Property for them.
- It speaks of "the restrictions on main".
- It uses $\APPLY$ ("the case of APPLY for a number operation"), which is defined in Chapter 6 and has no reference here.
A96 says "the property is stated at each level", but the book states it only in 4.9. Precedent: X12 accepted Chapter 4's mention of number specialisation.
Fix: move the module and program clause (and F2's definition) to Chapters 5 and 9. Replace APPLY with words ("the result of an arithmetic operation").

### F8 Minor: dynamic-core.tex:93-94 (A2)
"a variable that nothing at the occurrence fixes is $\tFloat$, as a variable left free in the program is below." The default now comes above (56-63), and line 107 says "by the default above".
Fix: change "below" to "above".

### F9 Minor: programs.tex:191-195 vs 213-218 (A6)
The Comment on r:p-stat-main-program says that with `init = \_ -> (0, Cmd.none)` "the model type is Float". The new paragraph uses the same `init` and says such a `main`, unannotated, does not elaborate. The first example leaves the flags undetermined.
Fix: use `init = \() -> (0, Cmd.none)` in the Comment, or say that `main` is annotated with flags ().

### F10 Minor: programs.tex:213-214 (A6)
"A flags type that the program leaves undetermined is therefore a type variable, which is not a port type". This is false when that variable is of class number. Dflt σ substitutes Float for it, and Float is a port type, so `init = \n -> (n + 1, Cmd.none)` elaborates with flags Float.
Fix: say "a type variable of a class other than number" (but see question Q2).

### F11 Minor: architecture/notation.md:296; architecture/book-plan.md:113, 227 (A1, seams)
- The `\pgDflt` registry row still reads "with Int for each bound type variable of class number".
- Book plan 113 still lists "unresolved `number` defaults to Int at top level (A27)" among static-core's further restrictions and does not mention principal derivations.
- Book plan 227 reads "A27 default applied to every undetermined number variable".
Fix: update the registry row and the plan rows.

### F12 Minor: static-core.tex:482, 485 (rulings convention)
"The labels of a row are distinct (A23)" and "(rule~\ruleref{r:s-dec-group}; A24)" print ruling IDs in the body. Rulings are cited in `% A<n>` comments, and the reader has no ambiguity log. Older examples of the same thing: effects.tex:374 "(A84)" and appendix-dynamic-basis.tex:459 "(A38)". Appendix E's tables cite rulings by design.
Fix: cite Section 4.3 (sec:static-core-types) and the Comment on r:s-dec-group instead.

### F13 Minor: static-core.tex:850-857 (wording of a correct claim)
I checked the claim that the restrictions give the same answer in every derivation against every pattern rule, and it holds; see "Verified" below. Three wording points:
- "every number specialisation of one" applies number specialisation (a translation of programs) to a derivation.
- The list "a special constant, a constructor, a tuple or a record pattern" leaves out `()` (r:s-atpat-unit), and `[]` and `::` unless they count as constructors.
- The argument speaks of "a part of the type of a match". Sub-patterns under a constructor elaborate at instances of constructor argument types, which are not parts of the match type: with `type W a = W (List a)`, `x :: xs` elaborates at `α List`.
Fix: write "where the principal derivation gives the type at which a sub-pattern elaborates as a type variable ...", list the unit, nil and cons patterns, and write "the derivation, and number specialisation, ...".

### F14 Minor: static-core.tex:360-363 vs 421-430; dynamic-core.tex:89-93 (A6)
Section 4.5 makes two schemes equal "by deleting bound variables that do not occur in the body". 4.8 (A93) closes a binding's scheme "also over" number variables that its type does not mention, and Chapter 6 relies on that: "Every binding ... quantifies all the variables of class number of the declaration, those its own type does not mention included ... so an instance assigns a type to each of them". By 4.5 that extra quantification is erased, and an instance (a type) assigns nothing to such a variable. The outcome is still fixed by "a variable that nothing at the occurrence fixes is Float".
Fix: exempt these variables from the deletion clause, or state A93 directly in Chapter 6 (the group's other number variables are Float at every occurrence of a binding whose type does not mention them).

### F15 Minor: appendix-implementation.tex:663
"All three conform." The table has two rows and two implementation columns, so it is unclear which three behaviours are meant.
Fix: "Both implementations conform in both cases."

### F16 Minor: static-core.tex:446-462 (A1)
The new metavariables D, D' (derivations) and S (substitutions) are not in notation.md.
Fix: register them.

## Verified (no finding)

- **The claim "the further restrictions give the same answer in every derivation" (A97).** Every pattern rule was checked.
  - These patterns elaborate only at a type that is not a variable:
    - r:s-atpat-scon (Int, Char or String);
    - r:s-atpat-con and r:s-pat-con (a ConsType);
    - r:s-atpat-unit (unit);
    - r:s-atpat-tuple (a tuple);
    - r:s-atpat-nil and r:s-pat-cons (a List type);
    - r:s-atpat-record (a RecType).
  - These elaborate at any τ, and each covers every inhabitant: r:s-atpat-wild, r:s-atpat-var, r:s-atpat-paren, r:s-pat-as, r:s-pat-atpat.
  - Row variables: record patterns cover every inhabitant, and a record type has the single inhabitant `_`, so instantiating a row changes nothing.
  - Every derivation is S applied to the principal one, so derivations differ only where the principal one has a variable. Only irrefutable sub-patterns occur there, and every type has an inhabitant (coinductive reading), so coverage and redundancy are preserved. The same holds under number specialisation: Float and a variable each have the single inhabitant `_`.
  - The claim depends on the Property (see F1 and F2), which holds at Core level.
- **The default copy and Dflt agree across chapters.** All of the following say Float:
  - static-core.tex:430 and 561-564;
  - dynamic-core.tex:56-110 (including the `check` example: the Int copy is 0 and the Float default copy has no value) and 420-424 (`inc (7 // 2)` is 4);
  - dynamic-modules.tex:75-79;
  - programs.tex:136-145, 191-195 and 229-237 (Dflt σ is the default copy's type);
  - appendix-dynamic-basis.tex:202, 527-540 (`abs -1.5` is 1.5, `abs (3 // -1)` is 3) and 622-624;
  - appendix-implementation.tex:604-664 and 1103-1105 (the `check` example: the Int copy has no value);
  - appendix-standard-ml.tex:115-122.
- **The A94 text in Appendix E** matches the ruling; the A56 and A87 divergence rows are removed, and no other text still calls them divergences.
- **The explicit-variable example** (dynamic-core.tex:66-71, `f : number -> number`, `g y = y + x`) is consistent with the closure section (4.8).

## Questions (not findings)

- Q1. Does Elm 0.19.1 accept a type declaration parameter named `number` (or `numberX`)? If it rejects one, F3 still holds for the book as written, but the fix could be a syntactic restriction instead.
- Q2. With an unannotated `main = Platform.worker { init = \n -> (n + 1, Cmd.none), ... }`, the principal flags type is a number variable, so Dflt gives Float and the program elaborates. Does Elm 0.19.1 accept it, or does it report BAD FLAGS? If it rejects it, A96 and Dflt disagree with Elm here.
- Q3. dynamic-core.tex:108-110 ("The default copy computes what an implementation with a single representation of numbers computes") describes implementations in the body (Hard Constraint 3). This is for part Y.
- Q4. A96's ruling text says the Property "is stated at each level", but the book states it once, in 4.9 (see F7). Should the ruling or the book change?
