module Mechanisation.View exposing (generatedPage, listPage, proofHref, proofPage, translationSection)

{-| The pages of the Lean proofs: the list of every theorem, a page for each, and a page for the
theorems generated at compile time. Like the rest of the book, they are put inside `View.freeze`.
-}

import Html exposing (Html)
import Html.Attributes as Attr
import Mechanisation exposing (Generated, GeneratedCheck, Method(..), Proof, ProofLink, ProofSummary, TranslatedCheck, Translation)
import Route
import Standard exposing (Index)
import Standard.ItemView as ItemView
import Standard.Render as Render


proofHref : String -> String
proofHref slug =
    Route.toString (Route.Standard__Proofs__Proof_ { proof = slug })


listHref : String
listHref =
    Route.toString Route.Standard__Proofs


title : String
title =
    "Lean proofs"


crumbs : Index -> Bool -> Html msg
crumbs idx onList =
    ItemView.crumbs idx
        (if onList then
            [ Html.text (" / " ++ title) ]

         else
            [ Html.text " / ", Html.a [ Attr.href listHref ] [ Html.text title ] ]
        )


{-| Text with `code` spans, as the doc comments write it.
-}
docText : String -> List (Html msg)
docText s =
    String.split "`" s
        |> List.indexedMap
            (\i part ->
                if modBy 2 i == 1 then
                    Html.code [] [ Html.text part ]

                else
                    Html.text part
            )


methodChip : Method -> Html msg
methodChip method =
    Html.span [ Attr.class "sd-method" ] [ Html.text (Mechanisation.methodName method) ]


pre : String -> Html msg
pre code =
    Html.pre [ Attr.class "sd-pre sd-lean" ] [ Html.code [] [ Html.text code ] ]


heading : String -> Html msg
heading text =
    Html.h2 [ Attr.class "sd-h sd-h1" ] [ Html.text text ]


ruleNumber : Index -> String -> Maybe Int
ruleNumber idx slug =
    List.filter (\r -> r.slug == slug) idx.rules |> List.head |> Maybe.map .number



-- THE LIST


listPage : Index -> Mechanisation.Index -> Html msg
listPage idx mech =
    Html.div [ Attr.class "sd-book" ]
        [ crumbs idx True
        , Html.h1 [ Attr.class "sd-chapter-title" ] [ Html.text title ]
        , Html.p [ Attr.class "sd-lede" ]
            [ Html.text ("The dynamic semantics of the Core, all " ++ String.fromInt mech.rules ++ " rules of ")
            , Html.a [ Attr.href (Render.chapterHref "dynamic-core" "") ] [ Html.text "Chapter 6" ]
            , Html.text ", and the arithmetic, equality, order and Boolean part of "
            , Html.em [] [ Html.text "APPLY" ]
            , Html.text (" are encoded in the proof assistant Lean 4 (" ++ mech.lean ++ "), one inductive relation per judgement and one constructor per rule. An evaluator for the same fragment is proved sound: whatever value it computes, the rules derive (")
            , Html.a [ Attr.href (proofHref "evExp_sound") ] [ Html.code [] [ Html.text "evExp_sound" ] ]
            , Html.text "). Every theorem below is checked by Lean each time the project is built, and each has a page with its statement and proof."
            ]
        , Html.p [ Attr.class "sd-p" ]
            [ Html.text "The evaluator is run on hand translations of test programs of this suite: a corpus of tests of the language, tests of the book's rulings, and tests of rules the corpus reaches only in passing"
            , case mech.checks of
                Just c ->
                    Html.text
                        (": "
                            ++ String.fromInt c.checks
                            ++ " checks, of which "
                            ++ String.fromInt c.agree
                            ++ " agree with the value the test expects"
                            ++ (if c.diverge > 0 then
                                    " and " ++ String.fromInt c.diverge ++ " are known divergences, where the book deliberately differs. "

                                else
                                    ". "
                               )
                        )

                Nothing ->
                    Html.text ". "
            , Html.a [ Attr.href (proofHref Mechanisation.generatedSlug) ]
                [ Html.text (String.fromInt mech.generatedCount ++ " further theorems") ]
            , Html.text " are generated when Lean compiles the project, one for each check whose value the kernel can compare, each proving that the rules derive the test's expected value."
            ]
        , Html.div [] (List.map (fileSection mech) mech.files)
        , Render.licence idx
        ]


fileSection : Mechanisation.Index -> { path : String, description : String } -> Html msg
fileSection mech file =
    let
        theorems =
            List.filter (\t -> t.file == file.path) mech.theorems

        sections =
            List.foldr
                (\t acc ->
                    case acc of
                        ( s, ts ) :: rest ->
                            if s == t.section then
                                ( s, t :: ts ) :: rest

                            else
                                ( t.section, [ t ] ) :: acc

                        [] ->
                            [ ( t.section, [ t ] ) ]
                )
                []
                theorems
    in
    Html.section [ Attr.class "ts-section" ]
        (heading file.path
            :: Html.p [ Attr.class "sd-also" ] (docText file.description)
            :: List.concatMap
                (\( section, ts ) ->
                    [ case section of
                        Just s ->
                            Html.h3 [ Attr.class "sd-h sd-h2" ] [ Html.text s ]

                        Nothing ->
                            Html.text ""
                    , Html.ul [ Attr.class "sd-list sd-proof-list" ] (List.map entry ts)
                    ]
                )
                sections
            ++ (if file.path == "StandardElmMech/Theorems.lean" then
                    [ Html.h3 [ Attr.class "sd-h sd-h2" ] [ Html.text "Generated at compile time" ]
                    , Html.ul [ Attr.class "sd-list sd-proof-list" ]
                        [ Html.li []
                            [ Html.a [ Attr.href (proofHref Mechanisation.generatedSlug) ]
                                [ Html.code [] [ Html.text ("kc_0 … kc_" ++ String.fromInt (mech.generatedCount - 1)) ] ]
                            , Html.text " "
                            , methodChip Kernel
                            , Html.div [ Attr.class "sd-proof-summary" ]
                                [ Html.text (String.fromInt mech.generatedCount ++ " theorems made by the command #kernel_checks, one per check of a test program.") ]
                            ]
                        ]
                    ]

                else
                    []
               )
        )


entry : ProofSummary -> Html msg
entry t =
    Html.li []
        [ Html.a [ Attr.href (proofHref t.slug) ] [ Html.code [] [ Html.text t.name ] ]
        , Html.text " "
        , methodChip t.method
        , if String.isEmpty t.summary then
            Html.text ""

          else
            Html.div [ Attr.class "sd-proof-summary" ] (docText t.summary)
        ]



-- ONE THEOREM


proofPage : Index -> Proof -> Html msg
proofPage idx p =
    let
        s =
            p.summary

        links label list =
            if List.isEmpty list then
                Html.text ""

            else
                Html.section [ Attr.class "ts-section" ]
                    [ heading label
                    , Html.ul [ Attr.class "sd-list" ]
                        (List.map (\l -> Html.li [] [ Html.a [ Attr.href (proofHref l.slug) ] [ Html.code [] [ Html.text l.name ] ] ]) list)
                    ]
    in
    Html.div [ Attr.class "sd-book" ]
        [ crumbs idx False
        , Html.h1 [ Attr.class "sd-chapter-title" ]
            [ Html.text "Theorem"
            , Html.code [ Attr.class "sd-rule-slug" ] [ Html.text s.name ]
            ]
        , Html.p [ Attr.class "sd-item-meta" ]
            [ Html.code [] [ Html.text (s.file ++ ":" ++ String.fromInt s.line) ]
            , Html.text
                (case s.section of
                    Just sec ->
                        ", " ++ sec ++ " · "

                    Nothing ->
                        " · "
                )
            , methodChip s.method
            ]
        , if String.isEmpty p.doc then
            Html.text ""

          else
            Html.p [ Attr.class "sd-lede" ] (docText p.doc)
        , heading "Statement"
        , pre p.statement
        , heading "Proof"
        , pre p.proof
        , methodNote s.method
        , if List.isEmpty p.tactics then
            Html.text ""

          else
            Html.section [ Attr.class "ts-section" ]
                (heading "Tactics it calls"
                    :: List.concatMap
                        (\t ->
                            [ Html.p [ Attr.class "sd-p" ]
                                (Html.code [] [ Html.text t.name ]
                                    :: Html.text (" (" ++ t.file ++ ":" ++ String.fromInt t.line ++ "): ")
                                    :: docText t.doc
                                )
                            , pre t.source
                            ]
                        )
                        p.tactics
                )
        , if List.isEmpty p.rules then
            Html.text ""

          else
            Html.section [ Attr.class "ts-section" ]
                [ heading "Rules of the book it uses"
                , Html.ul [ Attr.class "sd-list sd-proof-rules" ]
                    (List.map
                        (\r ->
                            Html.li []
                                [ Html.a [ Attr.href (Render.ruleHref r) ]
                                    [ Html.text
                                        (case ruleNumber idx r of
                                            Just n ->
                                                "(" ++ String.fromInt n ++ ") "

                                            Nothing ->
                                                ""
                                        )
                                    , Html.code [] [ Html.text r ]
                                    ]
                                ]
                        )
                        p.rules
                    )
                ]
        , links "Theorems it uses" p.uses
        , links "Used by" p.usedBy
        , if List.isEmpty p.rulings then
            Html.text ""

          else
            Html.p [ Attr.class "sd-also" ]
                [ Html.text ("About ruling" ++ plural p.rulings ++ " " ++ String.join ", " p.rulings ++ " of the book, where the implementations disagreed or were silent and the definition decides.") ]
        , Html.p [ Attr.class "sd-also" ]
            [ Html.text "In "
            , Html.code [] [ Html.text s.file ]
            , Html.text ": "
            , Html.span [] (docText p.fileDescription)
            , Html.text "."
            ]
        , Html.nav [ Attr.class "sd-pager" ]
            [ pager "Previous" p.prev
            , pager "Next" p.next
            ]
        , Render.licence idx
        ]


plural : List a -> String
plural list =
    if List.length list > 1 then
        "s"

    else
        ""


methodNote : Method -> Html msg
methodNote method =
    Html.p [ Attr.class "sd-also" ]
        [ Html.text
            (case method of
                Kernel ->
                    "Proved by decide +kernel: Lean's kernel itself runs the decision procedure, here the evaluator, and checks that the answer is true, so nothing outside the kernel is trusted."

                NativeDecide ->
                    "Proved by native_decide: the decision procedure is compiled and run, and its answer is trusted. This is used where values are compared as they print, floats above all, which the kernel cannot compare."

                Tactics ->
                    "Proved with tactics, which Lean expands into a proof term that its kernel checks."

                Term ->
                    "Proved by a term, which Lean's kernel checks directly."
            )
        ]


pager : String -> Maybe ProofLink -> Html msg
pager label maybe =
    case maybe of
        Just l ->
            Html.a [ Attr.class "sd-pager-link", Attr.href (proofHref l.slug) ]
                [ Html.span [ Attr.class "sd-pager-label" ] [ Html.text label ]
                , Html.code [] [ Html.text l.name ]
                ]

        Nothing ->
            Html.span [] []



-- THE GENERATED THEOREMS


generatedPage : Index -> Generated -> Html msg
generatedPage idx g =
    let
        n =
            String.fromInt

        code text =
            Html.code [] [ Html.text text ]

        proofLink name =
            Html.a [ Attr.href (proofHref name) ] [ code name ]

        step number heading_ content =
            Html.section [ Attr.class "ts-section" ]
                (Html.h2 [ Attr.class "sd-h sd-h1" ] [ Html.text (n number ++ ". " ++ heading_) ] :: content)

        para =
            Html.p [ Attr.class "sd-p" ]

        totalChecks =
            List.sum (List.map .checks g.groups)
    in
    Html.div [ Attr.class "sd-book" ]
        [ crumbs idx False
        , Html.h1 [ Attr.class "sd-chapter-title" ]
            [ Html.text "Theorems"
            , Html.code [ Attr.class "sd-rule-slug" ] [ Html.text ("kc_0 … kc_" ++ n (g.count - 1)) ]
            ]
        , Html.p [ Attr.class "sd-item-meta" ]
            [ Html.text (n g.count ++ " theorems generated at compile time · ")
            , methodChip Kernel
            ]
        , Html.p [ Attr.class "sd-lede" ]
            [ Html.text ("Each of these " ++ n g.count ++ " theorems states that the rules of ")
            , Html.a [ Attr.href (Render.chapterHref "dynamic-core" "") ] [ Html.text "Chapter 6" ]
            , Html.text " derive the value a test program expects for one of its checks. They are generated, not written by hand: none of them appears in the source. They are made from examples that were written by hand, as follows."
            ]
        , step 1
            "The examples are written by hand"
            [ para
                [ Html.text "Each example is a program translated by hand into Lean, in "
                , code "Examples.lean"
                , Html.text ". Nothing reads Elm: the translation is a Lean syntax tree of the bare Core, the book's syntax after its derived forms are taken away, built with small helper functions so that it reads much like the program. Each "
                , code "Debug.log \"label\" (exp)"
                , Html.text " of the program becomes one check, holding its label, the logged expression as a syntax tree, and the expected value copied from the program's "
                , code "-- CHECK: label: value"
                , Html.text " line. For example, the test ClosureCapture01Test"
                ]
            , pre "unwrapLater w =\n    \\dummy ->\n        case w of\n            Wrap x -> x\n\n_ = Debug.log \"unwrap1\" (unwrapLater (Wrap 42) 0)    -- CHECK: unwrap1: 42"
            , para [ Html.text "is written in Lean as" ]
            , pre "def pClosureCapture01 : Program := {\n  name := \"ClosureCapture01Test\",\n  cons := [(\"Wrap\", 1)],\n  defs := [ .fn \"unwrapLater\" [pv \"w\"]\n    (lams [pv \"dummy\"] (caseOf (v \"w\") [(pcon \"Wrap\" [pv \"x\"], v \"x\")])) ],\n  checks := [\n    ck \"unwrap1\" \"42\" (ap (v \"unwrapLater\") [ap (c \"Wrap\") [i 42], i 0]) ] }"
            , para
                [ Html.text "Every translated test shows its translation on its own page, under “Lean translation”, beside its Elm source. Because the translations are kept by hand, nothing guarantees that one matches its program; when the site is built, each translation's expected values are compared with the test's CHECK lines, and a difference is reported and marked on the test's page." ]
            ]
        , step 2
            "The examples are gathered in three lists"
            [ para
                [ Html.text "Lean's "
                , code "allPrograms"
                , Html.text " is the three lists of examples in turn, "
                , code "corpus ++ rulings ++ coverage"
                , Html.text (", " ++ n totalChecks ++ " checks in all:")
                ]
            , Html.div [ Attr.class "sd-table-wrap" ]
                [ Html.table [ Attr.class "ts-table" ]
                    [ Html.thead []
                        [ Html.tr []
                            [ Html.th [] [ Html.text "List" ]
                            , Html.th [] [ Html.text "Programs" ]
                            , Html.th [] [ Html.text "Checks" ]
                            , Html.th [] [ Html.text "Theorems generated" ]
                            ]
                        ]
                    , Html.tbody []
                        (List.map
                            (\gr ->
                                Html.tr []
                                    [ Html.td [] [ Html.text gr.title ]
                                    , Html.td [] [ Html.text (n gr.programs) ]
                                    , Html.td [] [ Html.text (n gr.checks) ]
                                    , Html.td [] [ Html.text (n gr.generated) ]
                                    ]
                            )
                            g.groups
                        )
                    ]
                ]
            , para
                [ Html.text "Every example is a test program of this suite, and every test it translates shows the translation on its page. A test that stops at Debug.todo, where the book says the expression has no value, is translated with the expected value “(no value)”." ]
            ]
        , step 3
            "Lean selects the checks the kernel can compare"
            [ para
                [ Html.text "The command "
                , code "#kernel_checks"
                , Html.text ", a metaprogram in Theorems.lean, runs while Lean compiles that file. It goes through the checks of "
                , code "allPrograms"
                , Html.text " in order and leaves out the checks whose expected value is not an Int, a constructor without arguments or a string:"
                ]
            , Html.ul [ Attr.class "sd-list" ]
                (List.filterMap identity
                    [ if g.skipped.divergence > 0 then
                        Just (Html.li [] [ Html.text (n g.skipped.divergence ++ " known divergences, where the book deliberately gives a different value from the one the check expects;") ])

                      else
                        Nothing
                    , Just (Html.li [] [ Html.text (n g.skipped.float ++ " checks of a float value, which is compared as it prints;") ])
                    , Just (Html.li [] [ Html.text (n g.skipped.value ++ " checks of a list, tuple, record or function, of a float written in a check, or of no value at all (a program that stops at Debug.todo).") ])
                    ]
                )
            , para
                [ Html.text ("That leaves " ++ n totalChecks ++ " − " ++ n (g.skipped.divergence + g.skipped.float + g.skipped.value) ++ " = " ++ n g.count ++ " checks. The ones left out are proved by ")
                , proofLink "corpus_derivable"
                , Html.text ", "
                , proofLink "rulings_derivable"
                , Html.text " and "
                , proofLink "coverage_derivable"
                , Html.text ", which compare values as they print and are proved by native_decide, except a check of no value: Lean's evaluator gives none, as the run of the examples checks, but the soundness theorem speaks only of the values the evaluator gives, so that is not a theorem."
                ]
            ]
        , step 4
            "Lean writes one theorem per check"
            [ para
                [ Html.text "For each check it keeps, the metaprogram writes the text of a theorem and has Lean elaborate it as if it were in the file. The theorems are numbered "
                , code "kc_0"
                , Html.text ", "
                , code "kc_1"
                , Html.text ", … in the order of the checks, so a theorem's number changes when an example is added or removed before it. The theorem for the check above is"
                ]
            , pre "/-- ClosureCapture01Test: unwrap1 = 42 -/\ntheorem kc_N : ∃ v, EvalExp env (phrase) v ∧ (Expect.int 42).holds v := by\n  first\n  | exact kcheck_sound (ch := false) (by decide +kernel)\n  | exact kcheck_sound (ch := true) (by decide +kernel)"
            , para
                [ Html.text "Here "
                , code "phrase"
                , Html.text " is the program's definitions placed in a "
                , code "let"
                , Html.text " around the logged expression, and "
                , code "env"
                , Html.text " is the initial environment with the program's constructors added. In words: there is a value v such that the rules derive "
                , Html.em [] [ Html.text "env ⊢ phrase ⇒ v" ]
                , Html.text ", and v is the integer 42."
                ]
            , case g.source of
                Just src ->
                    Html.details []
                        [ Html.summary [] [ Html.text ("The source of #kernel_checks (" ++ src.file ++ ":" ++ n src.line ++ ")") ]
                        , pre src.text
                        ]

                Nothing ->
                    Html.text ""
            ]
        , step 5
            "Lean's kernel proves each one"
            [ para
                [ Html.code [] [ Html.text "decide +kernel" ]
                , Html.text " has Lean's kernel itself run the mechanisation's evaluator on the phrase and check that the result is the expected value; nothing outside the kernel is trusted for this step. The evaluator is proved sound for the rules ("
                , proofLink "evExp_sound"
                , Html.text "), and "
                , proofLink "kcheck_sound"
                , Html.text " uses that to turn the kernel's computation into a derivation in the rules. Where the book lets an implementation choose between values ("
                , Html.em [] [ Html.text "APPLY" ]
                , Html.text " gives a set), the theorem tries both choices the evaluator can make."
                ]
            , para
                [ Html.text "All of this happens on every build of the Lean project: if an example changes, its theorems are generated afresh, and if the rules no longer derive an expected value, the build fails." ]
            ]
        , step 6
            "What they establish, and what they do not"
            [ para
                [ Html.text ("Together the " ++ n g.count ++ " theorems establish that, for each of these checks, the rules of Chapter 6 with the encoded part of APPLY derive exactly the value the check expects. They say this about the Lean translation of each program. That the translation is the same program as the Elm test rests on the care with which it was written, and on the comparison of expected values with the CHECK lines made when the site is built.") ]
            ]
        , Html.section [ Attr.class "ts-section" ]
            [ heading "The theorems"
            , Html.div [ Attr.class "sd-table-wrap" ]
                [ Html.table [ Attr.class "ts-table sd-kc-table" ]
                    [ Html.thead []
                        [ Html.tr []
                            [ Html.th [] [ Html.text "Theorem" ]
                            , Html.th [] [ Html.text "Program" ]
                            , Html.th [] [ Html.text "Check" ]
                            , Html.th [] [ Html.text "Value" ]
                            ]
                        ]
                    , Html.tbody [] (List.map generatedRow g.checks)
                    ]
                ]
            ]
        , Render.licence idx
        ]


generatedRow : GeneratedCheck -> Html msg
generatedRow c =
    Html.tr [ Attr.id c.name ]
        [ Html.td [] [ Html.code [] [ Html.text c.name ] ]
        , Html.td []
            [ case c.project of
                Just project ->
                    Html.a [ Attr.href (Route.toString (Route.Projects__Project___Test_ { project = project, test = c.program }) ++ "#lean") ]
                        [ Html.text c.program ]

                Nothing ->
                    Html.text c.program
            ]
        , Html.td [] [ Html.code [] [ Html.text c.label ] ]
        , Html.td [] [ Html.code [] [ Html.text c.expected ] ]
        ]



-- A TEST'S TRANSLATION


{-| The section of a test's page that shows its Lean translation, with what became of each check.
-}
translationSection : Translation -> Html msg
translationSection t =
    let
        code text =
            Html.code [] [ Html.text text ]

        drifted =
            List.filter (\c -> c.checkLine /= Just c.expected) t.checks

        listName =
            if t.group == "corpus" then
                "corpus of test programs"

            else if t.group == "rulings" then
                "tests of the book's rulings"

            else
                "tests for rules the corpus reaches only in passing"
    in
    Html.section [ Attr.class "ts-section", Attr.id "lean" ]
        [ Html.h2 [ Attr.class "ts-h2" ] [ Html.text "Lean translation" ]
        , Html.p [ Attr.class "ts-small" ]
            [ Html.text "This program is one of the examples of the "
            , Html.a [ Attr.href listHref ] [ Html.text "Lean mechanisation" ]
            , Html.text " of "
            , Html.em [] [ Html.text "A Standard Definition of Elm?" ]
            , Html.text (", in its " ++ listName ++ ". It was translated by hand into a Lean syntax tree of the bare Core (")
            , code (t.def ++ ", " ++ t.file ++ ":" ++ String.fromInt t.line)
            , Html.text "), with the expected values copied from its CHECK lines. Lean's evaluator runs the translation, and each check whose value the kernel can compare becomes a "
            , Html.a [ Attr.href (proofHref Mechanisation.generatedSlug) ] [ Html.text "generated theorem" ]
            , Html.text " that the book's rules derive that value."
            ]
        , if List.isEmpty drifted then
            Html.text ""

          else
            Html.p [ Attr.class "ts-small sd-lean-drift" ]
                [ Html.strong [] [ Html.text "Out of date. " ]
                , Html.text "The translation expects a value that is no longer the test's CHECK line for: "
                , Html.text (String.join ", " (List.map .label drifted))
                , Html.text ". The translation, and so its theorems, describe the test as it was."
                ]
        , Html.div [ Attr.class "sd-table-wrap" ]
            [ Html.table [ Attr.class "ts-table" ]
                [ Html.thead []
                    [ Html.tr []
                        [ Html.th [] [ Html.text "Check" ]
                        , Html.th [] [ Html.text "Expected (CHECK)" ]
                        , Html.th [] [ Html.text "Lean evaluator" ]
                        , Html.th [] [ Html.text "Proved by" ]
                        ]
                    ]
                , Html.tbody [] (List.map (translatedRow t) t.checks)
                ]
            ]
        , pre t.source
        , Html.p [ Attr.class "ts-muted ts-small" ]
            [ Html.text "Reading the translation: "
            , code "v \"x\""
            , Html.text " is the variable x, "
            , code "c \"K\""
            , Html.text " the constructor K, "
            , code "i 42"
            , Html.text " the integer 42 and "
            , code "str \"s\""
            , Html.text " a string; "
            , code "ap f [a, b]"
            , Html.text " applies f to a and then b, and "
            , code "bin \"+\" a b"
            , Html.text " is a + b. "
            , code "lams"
            , Html.text ", "
            , code "caseOf"
            , Html.text ", "
            , code "ifte"
            , Html.text ", "
            , code "listE"
            , Html.text ", "
            , code "tup2"
            , Html.text " and "
            , code "recE"
            , Html.text " build lambdas, case, if, lists, pairs and records by the book's derived forms; "
            , code "pv"
            , Html.text ", "
            , code "pw"
            , Html.text " and "
            , code "pcon"
            , Html.text " are variable, wildcard and constructor patterns. "
            , code "defs"
            , Html.text " are the program's top-level definitions, placed in a let around each check, and "
            , code "ck label value exp"
            , Html.text " is one check."
            ]
        ]


translatedRow : Translation -> TranslatedCheck -> Html msg
translatedRow t c =
    let
        derivedBy =
            if t.group == "corpus" then
                "corpus_derivable"

            else if t.group == "rulings" then
                "rulings_derivable"

            else
                "coverage_derivable"

        theoremLink name =
            Html.a [ Attr.href (proofHref name) ] [ Html.code [] [ Html.text name ] ]
    in
    Html.tr []
        [ Html.td [] [ Html.code [] [ Html.text c.label ] ]
        , Html.td []
            [ Html.code [] [ Html.text c.expected ]
            , case c.checkLine of
                Just now ->
                    if now == c.expected then
                        Html.text ""

                    else
                        Html.span [ Attr.class "sd-lean-drift" ] [ Html.text (" (the test now says " ++ now ++ ")") ]

                Nothing ->
                    Html.span [ Attr.class "sd-lean-drift" ] [ Html.text " (no longer a CHECK line of the test)" ]
            ]
        , Html.td []
            [ Html.code [] [ Html.text c.definition ]
            , Html.text
                (if c.status == "agree" then
                    ""

                 else
                    " (" ++ c.status ++ ")"
                )
            ]
        , Html.td []
            (case ( c.theorem, c.skipped ) of
                ( Just name, _ ) ->
                    [ Html.a [ Attr.href (proofHref Mechanisation.generatedSlug ++ "#" ++ name) ] [ Html.code [] [ Html.text name ] ] ]

                ( Nothing, Just "divergence" ) ->
                    [ Html.text "none: a known divergence" ]

                ( Nothing, Just "float" ) ->
                    [ theoremLink derivedBy, Html.text " (a float, compared as printed)" ]

                ( Nothing, _ ) ->
                    if c.expected == "(no value)" then
                        [ Html.text "no theorem: Lean's evaluator gives no value, as the run of the examples checks, but soundness speaks only of the values it gives" ]

                    else
                        [ theoremLink derivedBy, Html.text " (compared as printed)" ]
            )
        ]
