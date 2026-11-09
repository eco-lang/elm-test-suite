module SingleCtorPairCharFloatTest exposing (main)

{-| Values are extracted correctly from two single-constructor types in one module, one wrapping a `Char` and one wrapping a `Float`.

`unwrapChar` and `unwrapFloat` return the wrapped `'Z'` and `1.5`. `matchChar`
wraps a `Char`, matches it back out and returns the pair `( "got", 'Z' )`.

-}

-- TAGS: elm-spec, sm-conbind, d-pat-con, d-atpat-var
-- CHECK: unwrap_char: 'Z'
-- CHECK: unwrap_float: 1.5
-- CHECK: match_char: ("got",'Z')

import Html exposing (text)


type WrapChar
    = WrapChar Char


type WrapFloat
    = WrapFloat Float


unwrapChar : WrapChar -> Char
unwrapChar w =
    case w of
        WrapChar c ->
            c


unwrapFloat : WrapFloat -> Float
unwrapFloat w =
    case w of
        WrapFloat f ->
            f


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
        _ = Debug.log "unwrap_char" (unwrapChar (WrapChar 'Z'))
        _ = Debug.log "unwrap_float" (unwrapFloat (WrapFloat 1.5))
        _ = Debug.log "match_char" (matchChar 'Z')
    in
    text "done"
