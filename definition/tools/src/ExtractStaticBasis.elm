module ExtractStaticBasis exposing (run)

{-| Extracts Appendix C of A Standard Definition of Elm? and Figure fig:default-imports into
`definition/mechanisation/static-basis.json` (plans/lean-full-definition/step-07-classify.md, section
4) and `StandardElmMech/Generated/StaticBasis.lean` (step 9, section 6), and checks the translator's hand-written schemes (`Translate.Basis`) against it (section 6). Run
from the repository's root:

    site/node_modules/.bin/elm-pages run definition/tools/src/ExtractStaticBasis.elm
    site/node_modules/.bin/elm-pages run definition/tools/src/ExtractStaticBasis.elm --check

-}

import BackendTask exposing (BackendTask)
import BackendTask.Custom
import BackendTask.File
import Cli.Option as Option
import Cli.OptionsParser as OptionsParser
import Cli.Program as Program
import Dict exposing (Dict)
import FatalError exposing (FatalError)
import Json.Decode as Decode
import Json.Encode as Encode
import Pages.Script as Script exposing (Script)
import StaticBasis.Extract as Extract
import StaticBasis.Json exposing (Basis)
import StaticBasis.Lean
import StaticBasis.Latex exposing (Scheme, Ty(..))
import Translate.Basis as Basis
import Translate.Types as T


appendixPath : String
appendixPath =
    "definition/tex/appendix-static-basis.tex"


syntaxModulesPath : String
syntaxModulesPath =
    "definition/tex/syntax-modules.tex"


syntaxCorePath : String
syntaxCorePath =
    "definition/tex/syntax-core.tex"


outPath : String
outPath =
    "definition/mechanisation/static-basis.json"


type alias Options =
    { check : Bool }


config : Program.Config Options
config =
    Program.config
        |> Program.add (OptionsParser.build Options |> OptionsParser.with (Option.flag "check"))


read : String -> BackendTask FatalError String
read path =
    BackendTask.File.rawFile path |> BackendTask.allowFatal


sha256 : String -> BackendTask FatalError String
sha256 path =
    BackendTask.Custom.run "sha256File" (Encode.string path) Decode.string |> BackendTask.allowFatal


run : Script
run =
    Script.withCliOptions config
        (\options ->
            BackendTask.map5
                (\a sm sc sha1 sha2 -> { appendix = a, syntaxModules = sm, syntaxCore = sc, shas = [ ( appendixPath, sha1 ), ( syntaxModulesPath, sha2 ) ] })
                (read appendixPath)
                (read syntaxModulesPath)
                (read syntaxCorePath)
                (sha256 appendixPath)
                (sha256 syntaxModulesPath)
                |> BackendTask.andThen
                    (\src ->
                        case Extract.extract src of
                            Err e ->
                                BackendTask.fail (FatalError.fromString ("Appendix C: " ++ e))

                            Ok basis ->
                                let
                                    body =
                                        StaticBasis.Json.encodeBasis basis

                                    lean =
                                        StaticBasis.Lean.toLean basis

                                    check =
                                        basisCheck basis
                                in
                                Script.log (Extract.summary basis)
                                    |> BackendTask.andThen (\_ -> Script.log check.report)
                                    |> BackendTask.andThen
                                        (\_ ->
                                            if check.differ > 0 then
                                                BackendTask.fail (FatalError.fromString "Basis.elm differs from Appendix C")

                                            else if options.check then
                                                BackendTask.map2 Tuple.pair
                                                    (BackendTask.File.rawFile outPath |> BackendTask.toResult)
                                                    (BackendTask.File.rawFile StaticBasis.Lean.outPath |> BackendTask.toResult)
                                                    |> BackendTask.andThen
                                                        (\( r, rl ) ->
                                                            if r == Ok body && rl == Ok lean then
                                                                Script.log "static-basis.json and Generated/StaticBasis.lean are up to date."

                                                            else
                                                                Script.log "static-basis.json or Generated/StaticBasis.lean would change; run the extractor."
                                                        )

                                            else
                                                Script.writeFile { path = outPath, body = body }
                                                    |> BackendTask.allowFatal
                                                    |> BackendTask.andThen (\_ -> Script.writeFile { path = StaticBasis.Lean.outPath, body = lean } |> BackendTask.allowFatal)
                                                    |> BackendTask.andThen (\_ -> Script.log ("written: " ++ outPath ++ ", " ++ StaticBasis.Lean.outPath))
                                        )
                    )
        )



-- THE CHECK OF Translate.Basis (section 6)


classOfSpelling : String -> T.Class
classOfSpelling a =
    if String.startsWith "compappend" a then
        T.CompAppend

    else if String.startsWith "number" a then
        T.Number

    else if String.startsWith "comparable" a then
        T.Comparable

    else if String.startsWith "appendable" a then
        T.Appendable

    else
        T.Any


{-| Two schemes agree when a bijection of their variables preserving the class makes the bodies
equal.
-}
agree : Scheme -> T.Scheme -> Bool
agree s t =
    let
        classes =
            Dict.fromList t.quantified

        go : Ty -> T.Type -> ( Dict String Int, Dict Int String ) -> Maybe ( Dict String Int, Dict Int String )
        go a b ( fwd, bwd ) =
            case ( a, b ) of
                ( TyVar x, T.TVar i ) ->
                    case ( Dict.get x fwd, Dict.get i bwd ) of
                        ( Just j, Just y ) ->
                            if j == i && y == x then
                                Just ( fwd, bwd )

                            else
                                Nothing

                        ( Nothing, Nothing ) ->
                            if Dict.get i classes == Just (classOfSpelling x) || (Dict.get i classes == Nothing && classOfSpelling x == T.Any) then
                                Just ( Dict.insert x i fwd, Dict.insert i x bwd )

                            else
                                Nothing

                        _ ->
                            Nothing

                ( TyFn a1 a2, T.TFun b1 b2 ) ->
                    go a1 b1 ( fwd, bwd ) |> Maybe.andThen (go a2 b2)

                ( TyCon "Unit" [], T.TTuple [] ) ->
                    Just ( fwd, bwd )

                ( TyCon "Tuple2" args, T.TTuple bs ) ->
                    goList args bs ( fwd, bwd )

                ( TyCon "Tuple3" args, T.TTuple bs ) ->
                    goList args bs ( fwd, bwd )

                ( TyCon c args, T.TCon d bs ) ->
                    if c == d then
                        goList args bs ( fwd, bwd )

                    else
                        Nothing

                _ ->
                    Nothing

        goList xs ys acc =
            if List.length xs /= List.length ys then
                Nothing

            else
                List.foldl (\( x, y ) m -> Maybe.andThen (go x y) m) (Just acc) (List.map2 Tuple.pair xs ys)
    in
    go s.body t.t ( Dict.empty, Dict.empty ) /= Nothing


basisCheck : Basis -> { differ : Int, report : String }
basisCheck b =
    let
        iface m =
            b.modules |> List.filter (\i -> i.module_ == m) |> List.head

        valuesOf m =
            iface m |> Maybe.map (.ve >> List.filter (\v -> v.status == "v")) |> Maybe.withDefault []

        consOf m =
            iface m |> Maybe.map (.ve >> List.filter (\v -> v.status == "c")) |> Maybe.withDefault []

        compareOne name found expected =
            case found of
                Nothing ->
                    ( [], [ name ] )

                Just sch ->
                    if agree expected sch then
                        ( [ ( name, True ) ], [] )

                    else
                        ( [ ( name, False ) ], [] )

        results =
            List.map (\v -> compareOne ("Basics." ++ v.name) (Basis.value "" v.name) v.scheme) (valuesOf "Basics")
                ++ List.map (\v -> compareOne ("Debug." ++ v.name) (Basis.value "Debug" v.name) v.scheme) (valuesOf "Debug")
                ++ List.map (\v -> compareOne ("Char." ++ v.name) (Basis.value "Char" v.name) v.scheme) (valuesOf "Char")
                ++ List.map (\v -> compareOne (v.name) (Basis.constructor v.name) v.scheme) (consOf "Basics" ++ consOf "Maybe" ++ consOf "Result")
                ++ List.map (\o -> compareOne ("(" ++ o.op ++ ")") (Basis.operator o.op) o.scheme) b.operators

        compared =
            List.concatMap Tuple.first results

        differing =
            compared |> List.filter (not << Tuple.second) |> List.map Tuple.first

        absent =
            List.concatMap Tuple.second results

        bound =
            List.map .name (valuesOf "Basics")

        extra =
            Basis.valueNames |> List.filter (\n -> not (List.member n bound))
    in
    { differ = List.length differing
    , report =
        "Basis.elm against Appendix C: "
            ++ String.fromInt (List.length compared)
            ++ " compared, "
            ++ String.fromInt (List.length differing)
            ++ " differ."
            ++ (if List.isEmpty differing then
                    ""

                else
                    "\nDiffer: " ++ String.join ", " differing
               )
            ++ "\nAbsent from Basis.elm ("
            ++ String.fromInt (List.length absent)
            ++ "): "
            ++ String.join ", " absent
            ++ "\nIn Basis.elm but bound by no interface of ME0 ("
            ++ String.fromInt (List.length extra)
            ++ "): "
            ++ String.join ", " extra
    }
