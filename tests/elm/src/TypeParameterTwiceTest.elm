module TypeParameterTwiceTest exposing (main)

{-| A type's parameter list may not name the same type variable twice.

A Standard Definition of Elm?, restriction modules-tyvarseq-distinct: no type-variable sequence
contains the same variable twice. <https://elm-test-suite.netlify.app/standard/restrictions/modules-tyvarseq-distinct>

-}

-- TAGS: elm-spec, modules-tyvarseq-distinct
-- COMPILE-ERROR: a type parameter list with a repeated variable
-- CHECK: {{-- [A-Z ]+ -}}

import Html


type Pair a a
    = Pair a a


main =
    Html.text "done"
