module MinimalTypeAliasTest exposing (main)

{-| A type alias of a type name.

The simplest test of rules dm-topdec-alias, dm-typbind, sm-topdec-types of A Standard Definition of
Elm?: `type alias A = Int`, used in an annotation.
<https://elm-test-suite.netlify.app/standard/rules/dm-topdec-alias>

-}

-- TAGS: elm-spec, dm-topdec-alias, dm-typbind, sm-topdec-types
-- CHECK: testValue: 7

import Html exposing (text)


type alias A =
    Int


testValue : A
testValue =
    7


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
