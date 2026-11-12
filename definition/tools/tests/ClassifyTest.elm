module ClassifyTest exposing (suite)

{-| The static classification (plans/lean-full-definition/step-07-classify.md, section 7), on small
programs.
-}

import Elm.Parser
import Expect
import Set
import StaticBasis.Json as SB
import StaticBasis.Latex exposing (Ty(..))
import Test exposing (Test, describe, test)
import Translate.Classify as Classify


labels : Set.Set String
labels =
    Set.fromList [ "res:core-layout-rule", "res:modules-values-distinct", "r:s-exp-app" ]


mod : String -> String -> Classify.ModuleParse
mod name text =
    { path = "tests/elm/src/" ++ name ++ ".elm", name = name, file = Elm.Parser.parseToFile text |> Result.toMaybe }


err : List String -> List Classify.ModuleParse -> Classify.ErrorRecord
err tags modules =
    Classify.classifyError { labels = labels, overrides = [] }
        { project = "elm", name = "T", tags = tags, title = Nothing, modules = modules }


okModule : Classify.ModuleParse
okModule =
    mod "T" "module T exposing (main)\n\nimport Html exposing (text)\n\nmain =\n    text \"x\"\n"


{-| A small basis: Basics with `max`, Html with the type Html, and the default imports that matter.
-}
basis : SB.Basis
basis =
    { sources = []
    , typeNames = []
    , e0 = { te = [], ve = [] }
    , modules =
        [ { module_ = "Basics", library = "elm/core", te = [], ve = [ { name = "max", labels = [], scheme = { forall = [], body = TyCon "Int" [] }, status = "v" } ], ops = [] }
        , { module_ = "List", library = "elm/core", te = [], ve = [], ops = [ "::" ] }
        , { module_ = "Html", library = "elm/html", te = [ { tycon = "Html", labels = [], typeName = "Node", ve = [] } ], ve = [], ops = [] }
        , { module_ = "Platform.Cmd", library = "elm/core", te = [], ve = [ { name = "none", labels = [], scheme = { forall = [], body = TyCon "Int" [] }, status = "v" } ], ops = [] }
        ]
    , operators = []
    , hidden = []
    , defaultImports =
        [ { module_ = "Basics", as_ = Nothing, exposing_ = Just SB.ExposingAll }
        , { module_ = "List", as_ = Nothing, exposing_ = Just (SB.ExposingItems [ SB.ExpOp "::" ]) }
        , { module_ = "Platform.Cmd", as_ = Just "Cmd", exposing_ = Nothing }
        ]
    }


ok : Classify.ModuleParse -> Classify.SuccessRecord
ok m =
    Classify.classifySuccess basis { project = "elm", name = "T", modules = [ m ], helpers = Set.empty }


suite : Test
suite =
    describe "The static classification"
        [ test "a test whose helper does not parse is parse-fail" <|
            \_ -> (err [ "elm-spec", "s-exp-app" ] [ okModule, mod "H" "no header here" ]).class |> Expect.equal "parse-fail"
        , test "a parsed test whose rule is trusted to the parser is lexical-accepted" <|
            \_ -> (err [ "elm-spec", "core-layout-rule" ] [ okModule ]).class |> Expect.equal "lexical-accepted"
        , test "a syntactic restriction, the non-book tags skipped" <|
            \_ ->
                err [ "elm19-compile-error", "elm-spec", "modules-values-distinct" ] [ okModule ]
                    |> (\e -> ( e.class, e.rule, e.step ))
                    |> Expect.equal ( "syntactic", Just "res:modules-values-distinct", Just 8 )
        , test "a static rule is inference unless overridden" <|
            \_ -> (err [ "elm-spec", "s-exp-app" ] [ okModule ]).class |> Expect.equal "inference"
        , test "List.map is a library value; text from Html is the harness, main a view, not annotated" <|
            \_ ->
                Expect.all
                    [ \_ ->
                        ok (mod "T" "module T exposing (main)\n\nimport Html exposing (text)\n\nmain =\n    text (String.fromInt (List.length (List.map identity [ 1 ])))\n")
                            |> .needs
                            |> List.member "library:List.map"
                            |> Expect.equal True
                    , \_ ->
                        ok okModule
                            |> (\r -> ( r.basis, r.main, r.mainAnnotated ))
                            |> Expect.equal ( "harness", "view", False )
                    ]
                    ()
        , test "Cmd.none through the default import of Platform.Cmd as Cmd is no library use" <|
            \_ ->
                ok (mod "T" "module T exposing (main)\n\nimport Html exposing (text)\n\nx =\n    Cmd.none\n\nmain =\n    text \"x\"\n")
                    |> .needs
                    |> List.filter (String.startsWith "library:")
                    |> Expect.equal []
        ]
