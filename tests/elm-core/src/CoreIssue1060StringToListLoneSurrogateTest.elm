module CoreIssue1060StringToListLoneSurrogateTest exposing (main)

{-| `String.toList` of a string holding a lone low surrogate returns one `Char`.

<https://github.com/elm/core/issues/1060>

Elm 0.19.1 loops forever on `String.toList "\u{dd56}"` until it runs out of memory; the test caps
the JavaScript heap so that this fails quickly.

This test is probably wrong under A Standard Definition of Elm? It writes the lone surrogate as
the escape `"\u{dd56}"`, which ruling A8 makes invalid: an escape must denote a Unicode scalar
value. <https://elm-test-suite.netlify.app/standard/restrictions/core-escape-unicode> Under A8 the program does not compile, so a
compiler that follows the book fails this test without reaching the bug. `elm-core`'s
`StringToListLoneSurrogateTest` tests the same bug with the lone surrogate computed by
`Char.fromCode`. The test is kept as it is because it is the issue's program.

-}

-- TAGS: elm19-bug
-- CHECK: length: 1
-- ENV: NODE_OPTIONS=--max-old-space-size=256

import Html exposing (text)


main =
    let
        _ =
            Debug.log "length" (List.length (String.toList "\u{dd56}"))
    in
    text "done"
