module ImportResolutionQualifiedImportedFunctionTest exposing (..)

{-| A call written with the module qualifier, `Basics.negate`, resolves to the imported function even though the module is also imported with `exposing (..)`.

`xs` is `[ Basics.negate 1, Basics.negate 2 ]`, which `main` logs as `[-1,-2]`.

-}

-- TAGS: elm-spec, sm-imports-import, sm-explist-all, s-atexp-longvar
-- CHECK: testValue: [-1,-2]

import Basics exposing (..)
import Html


xs =
    [ Basics.negate 1, Basics.negate 2 ]


testValue =
    xs


main =
    let
        _ =
            Debug.log "testValue" testValue
    in
    Html.text "done"
