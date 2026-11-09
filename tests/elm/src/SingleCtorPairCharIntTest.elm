module SingleCtorPairCharIntTest exposing (main)

{-| Values are extracted correctly from two single-constructor types in one module, one wrapping a `Char` and one wrapping an `Int`.

`unwrapChar` and `unwrapInt` return the wrapped `'A'` and `256`. `matchChar`
wraps a `Char`, matches it back out and returns the pair `( "got", 'A' )`.

-}

-- TAGS: elm-spec, sm-conbind, d-pat-con, d-atpat-var
-- CHECK: unwrap_char: 'A'
-- CHECK: unwrap_int: 256
-- CHECK: match_char: ("got",'A')

import Html exposing (text)


type WrapChar
    = WrapChar Char


type WrapInt
    = WrapInt Int


unwrapChar : WrapChar -> Char
unwrapChar w =
    case w of
        WrapChar c ->
            c


unwrapInt : WrapInt -> Int
unwrapInt w =
    case w of
        WrapInt n ->
            n


matchChar : Char -> ( String, Char )
matchChar c =
    let
        w =
            WrapChar c
    in
    case w of
        WrapChar x ->
            ( "got", x )


main =
    let
        _ = Debug.log "unwrap_char" (unwrapChar (WrapChar 'A'))
        _ = Debug.log "unwrap_int" (unwrapInt (WrapInt 256))
        _ = Debug.log "match_char" (matchChar 'A')
    in
    text "done"
