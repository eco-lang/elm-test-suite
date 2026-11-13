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
            [ Html.text ("The dynamic semantics, " ++ String.fromInt mech.rules ++ " rules in all, of the Core (")
            , Html.a [ Attr.href (Render.chapterHref "dynamic-core" "") ] [ Html.text "Chapter 6" ]
            , Html.text "), of modules ("
            , Html.a [ Attr.href (Render.chapterHref "dynamic-modules" "") ] [ Html.text "Chapter 7" ]
            , Html.text "), of tasks, commands, subscriptions and ports ("
            , Html.a [ Attr.href (Render.chapterHref "effects" "") ] [ Html.text "Chapter 8" ]
            , Html.text ") and of the modules of a program ("
            , Html.a [ Attr.href (Render.chapterHref "programs" "") ] [ Html.text "Chapter 9" ]
            , Html.text "), and the arithmetic, equality, order, Boolean, conversion, append and character part of "
            , Html.em [] [ Html.text "APPLY" ]
            , Html.text (" are encoded in the proof assistant Lean 4 (" ++ mech.lean ++ "), one inductive relation per judgement and one constructor per rule. An evaluator for the same fragment is proved sound and complete: whatever value it computes, the rules derive (")
            , Html.a [ Attr.href (proofHref "evExp_sound") ] [ Html.code [] [ Html.text "evExp_sound" ] ]
            , Html.text "), and every derivation is found by it. Every theorem below is checked by Lean each time the project is built, and each has a page with its statement and proof."
            ]
        , Html.p [ Attr.class "sd-p" ]
            [ Html.text ("The evaluator is run on the test programs of this suite, translated into Lean by a program from their Elm source: " ++ String.fromInt (translatedCount mech) ++ " of the " ++ String.fromInt mech.coverage.total ++ " tests tagged elm-spec")
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
        , coverageSection mech
        , Html.div [] (List.map (fileSection mech) mech.files)
        , Render.licence idx
        ]


translatedCount : Mechanisation.Index -> Int
translatedCount mech =
    mech.coverage.reasons |> List.filter (\r -> r.reason == "translated") |> List.map .count |> List.sum


{-| The `elm-spec` tests by whether they are translated into Lean, and why not.
-}
coverageSection : Mechanisation.Index -> Html msg
coverageSection mech =
    Html.section [ Attr.class "ts-section" ]
        [ heading "Which tests are translated"
        , Html.p [ Attr.class "sd-p" ]
            [ Html.text ("Every one of the " ++ String.fromInt mech.coverage.total ++ " tests tagged elm-spec is either translated into Lean, by the translator definition/tools/src/Translate.elm, or not, for one of the reasons below. A test that expects a compile error has no meaning to run, so it is not translated; its refusal is proved in Lean from its source instead. A value or module of the basis that the encoding does not include keeps a test out until the encoding includes it.") ]
        , Html.div [ Attr.class "sd-table-wrap" ]
            [ Html.table [ Attr.class "ts-table" ]
                [ Html.thead [] [ Html.tr [] [ Html.th [] [ Html.text "Tests" ], Html.th [] [ Html.text "Status" ] ] ]
                , Html.tbody []
                    (List.map
                        (\r ->
                            Html.tr []
                                [ Html.td [] [ Html.text (String.fromInt r.count) ]
                                , Html.td []
                                    [ Html.details []
                                        [ Html.summary [] [ Html.text (reasonWords r.reason) ]
                                        , Html.p [ Attr.class "ts-small" ]
                                            (List.intersperse (Html.text ", ")
                                                (List.map
                                                    (\t -> Html.a [ Attr.href (Route.toString (Route.Projects__Project___Test_ { project = t.project, test = t.name }) ++ "#lean") ] [ Html.text t.name ])
                                                    r.tests
                                                )
                                            )
                                        ]
                                    ]
                                ]
                        )
                        mech.coverage.reasons
                    )
                ]
            ]
        ]


{-| A refusal reason of the translator, in words.
-}
reasonWords : String -> String
reasonWords reason =
    let
        after p =
            String.dropLeft (String.length p) reason
    in
    if reason == "translated" then
        "translated"

    else if reason == "compile-error" then
        "expects a compile error, so it has no meaning to evaluate; its refusal is proved from the source syntax (below), unless elm-syntax rejects the program or loses the error"

    else if reason == "effects" then
        "uses effects the encoding does not include"

    else if reason == "parse" then
        "is not parsed by elm-syntax 7.3.9"

    else if reason == "type" then
        "the translator's inference does not type it"

    else if reason == "number" then
        "number specialisation could not decide a literal"

    else if reason == "basis:Basics.pow@Float" then
        "uses ^ at Float, which the encoding does not include"

    else if String.startsWith "basis:" reason then
        "uses " ++ after "basis:" ++ ", which the encoding does not include"

    else if String.startsWith "import:" reason then
        "imports " ++ after "import:" ++ ", a library module the encoding does not include"

    else if reason == "construct:large-program" || reason == "construct:large-type" then
        "tests a compiler's limits, with a program or type too large to encode"

    else if reason == "construct:record-alias-constructor" then
        "uses a record type alias as a constructor"

    else if reason == "construct:main-shape" then
        "its main is not a let of checks"

    else if String.startsWith "construct:" reason then
        "uses a construct the translator does not handle (" ++ after "construct:" ++ ")"

    else if String.startsWith "checks:" reason then
        "its CHECK lines cannot be matched one to one with its logged checks (" ++ after "checks:" ++ ")"

    else
        reason


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
                                [ Html.code [] [ Html.text "kc_<Shard>_<n>" ] ]
                            , Html.text " "
                            , methodChip Kernel
                            , Html.div [ Attr.class "sd-proof-summary" ]
                                [ Html.text (String.fromInt mech.generatedCount ++ " theorems made by the command #kernel_checks, one per check of a translated test that the kernel can compare.") ]
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

        programs =
            List.sum (List.map .programs g.groups)
    in
    Html.div [ Attr.class "sd-book" ]
        [ crumbs idx False
        , Html.h1 [ Attr.class "sd-chapter-title" ]
            [ Html.text "Theorems"
            , Html.code [ Attr.class "sd-rule-slug" ] [ Html.text "t_<project>_<Test>" ]
            ]
        , Html.p [ Attr.class "sd-item-meta" ]
            [ Html.text (n programs ++ " program theorems, covering " ++ n g.count ++ " checks, generated at compile time · ")
            , methodChip Kernel
            ]
        , Html.p [ Attr.class "sd-lede" ]
            [ Html.text "Each of these theorems states that a test program, evaluated by the rules of "
            , Html.a [ Attr.href (Render.chapterHref "dynamic-core" "") ] [ Html.text "Chapters 6, 7 and 9" ]
            , Html.text ", logs the value each of its checks expects, or, for a program that stops at Debug.todo, has no meaning. Nothing about them is written by hand: the test programs are translated into Lean by a program, and the theorems are written by Lean from the translations, as follows."
            ]
        , step 1
            "The translator turns each test into Lean"
            [ para
                [ Html.text "The translator, "
                , code "definition/tools/src/Translate.elm"
                , Html.text ", reads every test tagged elm-spec. It parses the program with elm-syntax, resolves its names, works out the type of every number constant by the book's number specialisation, and prints each module of the program as a Lean syntax tree of the bare Core (the derived forms of Appendix A applied by "
                , code "Derived.lean"
                , Html.text "), with its exposing list, imports, custom types and aliases. Each "
                , code "-- CHECK: label: value"
                , Html.text " line of the test becomes a check on what the program logs. A test outside what the encoding covers is not translated, and its page says why. For example, the test ClosureCapture01Test"
                ]
            , pre "unwrapLater w =\n    \\dummy ->\n        case w of\n            Wrap x -> x\n\n_ = Debug.log \"unwrap1\" (unwrapLater (Wrap 42) 0)    -- CHECK: unwrap1: 42"
            , para [ Html.text "becomes" ]
            , pre "def g_elm_ClosureCapture01Test : Program := {\n  name := \"ClosureCapture01Test\", source := \"tests/elm/src\",\n  exposing := (.items [.var \"main\"]), imports := [⟨\"Html\", \"Html\", some (.items [.var \"text\"])⟩],\n  types := [(\"Wrapper\", [(\"Wrap\", 1)])],\n  defs := [\n    .fn \"unwrapLater\" [pv \"w\"] (lams [pv \"dummy\"] (caseOf (v \"w\") [(pcon \"Wrap\" [pv \"x\"], v \"x\")])),\n    .fn \"main\" [] (letDefs [ ... Debug.log \"unwrap1\" ... ] ...) ],\n  checks := [\n    chk .check \"unwrap1: 42\" .int,\n    chk .check \"unwrap2: 99\" .int ] }"
            , para
                [ Html.text "Every translated test shows its translation on its own page, under “Lean translation”, beside its Elm source. The translations are generated again whenever the mechanisation is rebuilt, so they follow their tests; a page whose test has changed since says so." ]
            ]
        , step 2
            "The translations are gathered in shards"
            [ para
                [ Html.text ("The translated programs are written in files of at most 40, called shards, so that Lean builds them in parallel; " ++ n programs ++ " programs and " ++ n totalChecks ++ " checks in all:") ]
            , Html.div [ Attr.class "sd-table-wrap" ]
                [ Html.table [ Attr.class "ts-table" ]
                    [ Html.thead []
                        [ Html.tr []
                            [ Html.th [] [ Html.text "Shard" ]
                            , Html.th [] [ Html.text "Programs" ]
                            , Html.th [] [ Html.text "Checks" ]
                            , Html.th [] [ Html.text "Checks in a theorem" ]
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
            ]
        , step 3
            "Lean writes one theorem per program"
            [ para
                [ Html.text "Each shard has a file of theorems, "
                , code "Generated/Checks<Shard>.lean"
                , Html.text ", in which the command "
                , code "#mod_program_theorems"
                , Html.text ", a metaprogram in Theorems.lean, runs while Lean compiles the file. For each program of the shard it writes the text of one theorem and has Lean elaborate it as if it were in the file:"
                ]
            , pre "theorem t_elm_ClosureCapture01Test :\n    Mod.ViewChecks (Mod.Btest []) g_elm_ClosureCapture01Test.modules [checks] :=\n  Mod.viewChecks_sound (o := .const false) (by decide +kernel)"
            , para
                [ Html.text "In words: the program's modules, evaluated by Chapter 7's rules in the test basis, have a derivation whose log meets every check. For a program the test expects to stop at Debug.todo the theorem is instead "
                , code "Mod.NoMeaning (Mod.Btest []) g.modules"
                , Html.text ", by "
                , code "Mod.noMeaning_sound"
                , Html.text ": no derivation gives it a meaning. Where the book lets an implementation choose ("
                , Html.em [] [ Html.text "APPLY" ]
                , Html.text " gives a set), the theorem names the choice that meets the checks."
                ]
            , case g.source of
                Just src ->
                    Html.details []
                        [ Html.summary [] [ Html.text ("The source of #mod_program_theorems (" ++ src.file ++ ":" ++ n src.line ++ ")") ]
                        , pre src.text
                        ]

                Nothing ->
                    Html.text ""
            ]
        , step 4
            "Lean's kernel proves each one"
            [ para
                [ Html.code [] [ Html.text "decide +kernel" ]
                , Html.text " has Lean's kernel itself run the mechanisation's evaluator on the program and check its log against the checks; nothing outside the kernel is trusted for this step. The evaluator is proved sound for the rules ("
                , proofLink "evExp_sound"
                , Html.text "), and the lemmas named above turn the kernel's computation into a statement about the rules. "
                , Html.text (n g.skipped.native ++ " checks belong to programs proved by native_decide instead, tagged [native]: programs that use a value only the C library computes (round, floor, an elementary function, ^ at Float, Debug.toString), or whose proof breaks the memory budget.")
                ]
            , para
                [ Html.text "All of this happens on every build of the Lean project: when a test changes, the translator writes its new translation, its theorem is generated afresh, and if the rules no longer give an expected value, the build fails." ]
            ]
        , step 5
            "What they establish, and what they do not"
            [ para
                [ Html.text ("Together the theorems establish that, for each of these " ++ n g.count ++ " checks, the rules with the encoded part of APPLY give exactly the value the check expects. A check of what a program logs before it stops at Debug.todo is in no theorem (its program's theorem says only that it has no meaning); the run of the examples compares it. Each theorem is about the Lean translation of its program, which the translator makes; for the translated tests, the end-to-end theorem on the test's page shows that Lean computes the same translation from the source.") ]
            ]
        , Html.section [ Attr.class "ts-section" ]
            [ heading "The checks and their theorems"
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


{-| The section's paragraphs, then the paragraph on the test's static and end-to-end theorems. -}
staticsAfter : Translation -> List (Html msg) -> List (Html msg)
staticsAfter t paras =
    paras ++ staticsParas t


{-| What plans steps 9 to 11 prove about the test: its static theorem (`legal_`, without hypothesis
since step 11 except where `conditional` keeps D11, or `refuse_`, for every derivation) and, for a translated test, its end-to-end theorems, which retire
the trust in the translator's elaboration ([elab]) for that test. The theorems are in
`StandardElmMech/Certs/`, written by `lake exe certify`.
-}
staticsParas : Translation -> List (Html msg)
staticsParas t =
    let
        code text =
            Html.code [] [ Html.text text ]

        nativeNote =
            case t.statics of
                Just s ->
                    if s.native then
                        " One of these theorems is proved by native_decide ([native])."

                    else
                        ""

                Nothing ->
                    ""
    in
    case t.statics of
        Nothing ->
            []

        Just s ->
            [ Html.p [ Attr.class "ts-small" ]
                (List.concat
                    [ case s.legal of
                        Just n ->
                            [ Html.text "Static semantics (Chapters 4, 5 and 9): "
                            , code n
                            , Html.text
                                (if s.conditional then
                                    " states that the program as written is legal, if the derivation Lean's inference finds is principal ([principal]; the proved inference W gave no result on this program within the time allowed): it meets the syntactic restrictions, and each module elaborates by a derivation the proved checker accepts, meeting the further restrictions, with a type of main Chapter 9 allows. "

                                 else
                                    " states that the program as written is legal, with no hypothesis: the proved inference W gives each module a principal derivation, which meets the syntactic restrictions and the further restrictions, with a type of main Chapter 9 allows. "
                                )
                            ]

                        Nothing ->
                            []
                    , case s.refuse of
                        Just n ->
                            [ Html.text "Static semantics (Chapters 4, 5 and 9, and the syntactic restrictions): "
                            , code n
                            , Html.text " states that the program is not legal, for every derivation, with no hypothesis about principality. "
                            ]

                        Nothing ->
                            []
                    , case s.spec of
                        Just n ->
                            [ Html.text "End to end: "
                            , code n
                            , Html.text " states that Lean computes the reduced program above from the source (derived forms, inference, the proved checker, number specialisation, type erasure), so the theorems about it do not trust the translator's elaboration ([elab]); "
                            ]
                                ++ (case s.mean of
                                        Just m ->
                                            [ code m, Html.text " states that the program has a meaning by r:p-program, with both premises" ]
                                                ++ (case s.ident of
                                                        Just i ->
                                                            [ Html.text ", and ", code i, Html.text " that its specialisation is unique and is the reduced program above, both with no hypothesis about principality." ]

                                                        Nothing ->
                                                            [ Html.text "." ]
                                                   )

                                        Nothing ->
                                            [ Html.text "the program has no meaning (it stops at Debug.todo)." ]
                                   )

                        Nothing ->
                            []
                    , [ Html.text nativeNote ]
                    ]
                )
            ]


{-| The section of an `elm-spec` test's page about its Lean translation: the translation with what
became of each check, or why the test is not translated.
-}
translationSection : Translation -> Html msg
translationSection t =
    let
        code text =
            Html.code [] [ Html.text text ]

        drifted =
            List.filter (\c -> c.checkLine /= Just c.expected) t.checks
    in
    Html.section [ Attr.class "ts-section", Attr.id "lean" ]
        (staticsAfter t <|
            Html.h2 [ Attr.class "ts-h2" ] [ Html.text "Lean translation" ]
            :: (case t.status of
                    "refused" ->
                        [ Html.p [ Attr.class "ts-small" ]
                            [ Html.text "Not translated into Lean: it "
                            , Html.text (reasonWords (Maybe.withDefault "" t.reason))
                            , Html.text ". See "
                            , Html.a [ Attr.href listHref ] [ Html.text "the Lean mechanisation" ]
                            , Html.text " for which tests are translated, and why."
                            ]
                        ]

                    _ ->
                        [ Html.p [ Attr.class "ts-small" ]
                            (if t.status == "hand" then
                                [ Html.text "The translator does not translate this program (it "
                                , Html.text (reasonWords (Maybe.withDefault "" t.reason))
                                , Html.text "), so the checks it can express are translated by hand ("
                                , code (t.def ++ ", " ++ t.file)
                                , Html.text "), with the expected values copied from its CHECK lines. Lean's evaluator runs the translation, and each check whose value the kernel can compare becomes a "
                                , Html.a [ Attr.href (proofHref Mechanisation.generatedSlug) ] [ Html.text "generated theorem" ]
                                , Html.text "."
                                ]

                             else if t.kind == "worker" then
                                [ Html.text "This worker program is translated into Lean by the translator of the "
                                , Html.a [ Attr.href listHref ] [ Html.text "Lean mechanisation" ]
                                , Html.text " of "
                                , Html.em [] [ Html.text "A Standard Definition of Elm?" ]
                                , Html.text (" (" ++ t.def ++ ", in " ++ t.file ++ "). Lean evaluates its modules by the rules of Chapter 7, starts it by r:p-init with ")
                                , case t.flags of
                                    Just f ->
                                        Html.span [] [ Html.text "the flags ", code f ]

                                    Nothing ->
                                        Html.text "no flags (null, A72)"
                                , Html.text
                                    (", and runs it by the transitions of Chapter 9 under "
                                        ++ (if t.host == Just "echo" then
                                                "the test runner's echo host, which sends every value delivered on echoOut back on echoIn, in order"

                                            else
                                                "a host that sends nothing"
                                           )
                                        ++ ". Its checks become one "
                                    )
                                , Html.a [ Attr.href (proofHref Mechanisation.generatedSlug) ] [ Html.text "generated theorem" ]
                                , Html.text
                                    (": some execution the book allows, under that host, has a log (the modules', then the start's, then each step's) that meets every check. The theorem trusts the parser and the translator's elaboration ([parse] [elab]), the test basis ([harness]) and the parameters of the basis ([params])"
                                        ++ (if t.native then
                                                ", and is proved by native_decide ([native])."

                                            else
                                                ", and is proved by the kernel."
                                           )
                                    )
                                ]
                                    ++ List.concatMap
                                        (\d ->
                                            [ Html.text " Not stated: ", code d, Html.text "." ]
                                        )
                                        t.dropped

                             else
                                [ Html.text "This program is translated into Lean by the translator of the "
                                , Html.a [ Attr.href listHref ] [ Html.text "Lean mechanisation" ]
                                , Html.text " of "
                                , Html.em [] [ Html.text "A Standard Definition of Elm?" ]
                                , Html.text (": the program it is, its modules in the reduced syntax of Chapter 7 with every integer constant at Int or Float by number specialisation, and its CHECK lines as written (" ++ t.def ++ ", in " ++ t.file ++ "). Lean's evaluator runs the program by the rules of Chapters 7 and 9, and its "
                                    ++ (if List.length t.sources > 1 then "modules' " else "")
                                    ++ "checks become one "
                                  )
                                , Html.a [ Attr.href (proofHref Mechanisation.generatedSlug) ] [ Html.text "generated theorem" ]
                                , Html.text ": some derivation of the program has a log that meets every check, or, for a test that stops at Debug.todo, the program has no meaning."
                                ]
                                    ++ (if List.length t.sources > 1 then
                                            [ Html.text " Its modules, in program order: "
                                            , Html.text (String.join ", " t.sources)
                                            , Html.text "."
                                            ]

                                        else
                                            []
                                       )
                            )
                        , if t.current && List.isEmpty drifted then
                            Html.text ""

                          else
                            Html.p [ Attr.class "ts-small sd-lean-drift" ]
                                [ Html.strong [] [ Html.text "Out of date. " ]
                                , Html.text "The test, or a module it imports, has changed since this translation was made; the translation, and so its theorems, describe the program as it was until the mechanisation is rebuilt."
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
                            , Html.text " the integer 42 at Int, "
                            , code ".scon (.intF 2)"
                            , Html.text " the integer 2 at Float, and "
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
                            , Html.text " are the program's top-level definitions and "
                            , code "locals"
                            , Html.text " the other declarations of main's let, placed in a let around each check; "
                            , code "ckk label value kind exp"
                            , Html.text " is one check. A name with $ (incF$Float) is a copy number specialisation made."
                            ]
                        ]
               )
        )


translatedRow : Translation -> TranslatedCheck -> Html msg
translatedRow t c =
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
                (if String.startsWith "agree" c.status then
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

                ( Nothing, Just "partial-log" ) ->
                    [ Html.text "no theorem: the program stops at Debug.todo, and its theorem says only that it has no meaning; the run of the examples compares what it logs first" ]

                ( Nothing, _ ) ->
                    [ Html.text "no theorem: compared by the run of the examples" ]
            )
        ]
