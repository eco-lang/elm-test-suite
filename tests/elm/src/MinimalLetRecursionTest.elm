module MinimalLetRecursionTest exposing (main)

{-| A let definition of a function that calls itself.

The simplest test of rule d-dec-rec of A Standard Definition of Elm?: `f` walks to the end of a
one-element list and returns `0`; its declaration refers to `f`, so it is recursive.
<https://elm-test-suite.netlify.app/standard/rules/d-dec-rec>

-}

-- TAGS: elm-spec, d-dec-rec
-- CHECK: testValue: 0

import Html exposing (text)


testValue =
    let
        f l =
            case l of
                [] ->
                    0

                _ :: rest ->
                    f rest
    in
    f [ 1 ]


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
