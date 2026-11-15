module ArrayEqualityFlagsTest exposing (main)

{-| Two arrays are equal under `==` when they hold equal elements in the same order: arrays
received as flags are compared, with the same elements, a different element, and a different
length.

A Standard Definition of Elm? gives arrays as the lists of their elements (Appendix D, Arrays),
compared by the fourth clause of the equality of values: equal exactly when their lists are. An
array reaches a program within the definition only through its flags or a port, so the four
arrays are the flags, a JSON object decoded at a record of `Array Int` fields.
`ArrayAppendCanonicalTest` and `ArrayEqAfterPushTest` compare arrays built by elm/core's library
functions.

-}

-- TAGS: elm-spec, b:Basics.eq, b:Basics.neq, b:Array.Array, fig:dynamic-basis-eq
-- FLAGS: {"a":[1,2,3],"b":[1,2,3],"c":[1,2,4],"d":[1,2]}
-- CHECK: same: True
-- CHECK: differentElement: False
-- CHECK: differentLength: False
-- CHECK: notEqualSame: False

import Array exposing (Array)
import Platform


type alias Flags =
    { a : Array Int
    , b : Array Int
    , c : Array Int
    , d : Array Int
    }


init : Flags -> ( (), Cmd msg )
init flags =
    let
        _ =
            Debug.log "same" (flags.a == flags.b)

        _ =
            Debug.log "differentElement" (flags.a == flags.c)

        _ =
            Debug.log "differentLength" (flags.a == flags.d)

        _ =
            Debug.log "notEqualSame" (flags.a /= flags.b)
    in
    ( (), Cmd.none )


main : Program Flags () msg
main =
    Platform.worker
        { init = init
        , update = \_ model -> ( model, Cmd.none )
        , subscriptions = \_ -> Sub.none
        }
