module TailRecCaseMultiBranchTypesTest exposing (main)

{-| A self tail-recursive search whose outer `case` has one branch per constructor of a
custom type at the head of a list, with a nested `case` on a `String` inside one branch,
finds the right element.

`findEndianness` walks a list of `Expr`, counting positions from `idx`, and stops at the
first `Var "LE"` or `Var "BE"`; every other element is skipped by a tail call. In
`[ Lit 1, Call "foo" [], Var "LE", Var "other" ]` that is position 2, returned as
`FoundLE 2`.
-}

-- TAGS: elm-spec, d-pat-cons, d-pat-con, d-pat-con-fail, d-atpat-scon
-- CHECK: result: FoundLE 2

import Html exposing (text)


type Expr
    = Var String
    | Call String (List Expr)
    | Lit Int


type Found
    = FoundLE Int
    | FoundBE Int
    | NotFound


findEndianness : List Expr -> Int -> Found
findEndianness exprs idx =
    case exprs of
        [] ->
            NotFound

        (Var name) :: rest ->
            case name of
                "LE" ->
                    FoundLE idx

                "BE" ->
                    FoundBE idx

                _ ->
                    findEndianness rest (idx + 1)

        (Call _ _) :: rest ->
            findEndianness rest (idx + 1)

        (Lit _) :: rest ->
            findEndianness rest (idx + 1)


main =
    let
        exprs =
            [ Lit 1, Call "foo" [], Var "LE", Var "other" ]

        _ = Debug.log "result" (findEndianness exprs 0)
    in
    text "done"
