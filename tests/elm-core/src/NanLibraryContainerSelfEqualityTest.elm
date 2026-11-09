module NanLibraryContainerSelfEqualityTest exposing (main)

{-| An `Array`, `Dict` or `Set` holding NaN is not equal to itself.

<https://github.com/elm/core/issues/988>

NaN is not equal to anything, itself included, so no container holding NaN can be equal to
anything. Elm 0.19.1's `_Utils_eq` returns True as soon as `x === y`, before it looks inside, so a
container compared with itself is True. These containers are built by library functions
(`Array.fromList`, `Dict.fromList`, `Set.fromList`); the containers of the language are checked by
CoreIssue988NanContainerSelfEqualityTest.

-}

-- TAGS: elm19-bug
-- CHECK: array: False
-- CHECK: dict: False
-- CHECK: set: False

import Array
import Dict
import Html exposing (text)
import Set


main =
    let
        nan =
            0 / 0

        array =
            Array.fromList [ nan ]

        dict =
            Dict.fromList [ ( 1, nan ) ]

        set =
            Set.fromList [ nan ]

        _ =
            Debug.log "array" (array == array)

        _ =
            Debug.log "dict" (dict == dict)

        _ =
            Debug.log "set" (set == set)
    in
    text "done"
