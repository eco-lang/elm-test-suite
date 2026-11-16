module MinimalCustomTypeTest exposing (main)

{-| A custom type with one constructor.

The simplest test of rules dm-conbind, dm-datbind, dm-topdec-type of A Standard Definition of Elm?:
`type T = A`, and the value `A`. <https://elm-test-suite.netlify.app/standard/rules/dm-conbind>

-}

-- TAGS: elm-spec, dm-conbind, dm-datbind, dm-topdec-type
-- CHECK: testValue: A

import Html exposing (text)


type T
    = A


testValue =
    A


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    text "done"
