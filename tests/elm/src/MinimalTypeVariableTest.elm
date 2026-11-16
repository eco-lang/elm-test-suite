module MinimalTypeVariableTest exposing (main)

{-| An annotation with a type variable.

The simplest test of rules s-ty-tyvar, s-ty-fun of A Standard Definition of Elm?: `same : a -> a`
annotates the identity function, used at `7`.
<https://elm-test-suite.netlify.app/standard/rules/s-ty-tyvar>

-}

-- TAGS: elm-spec, s-ty-tyvar, s-ty-fun
-- CHECK: testValue: 7

import Html exposing (text)


same : a -> a
same x =
    x


testValue =
    same 7


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
