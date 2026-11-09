module CompilerIssue1748DestructureMissingFieldCrashTest exposing (..)

{-| Destructuring a record field that does not exist, in an unannotated function, crashes the compiler.

<https://github.com/elm/compiler/issues/1748>

Elm 0.19.1 crashes ("index out of bounds") on this program. It should report a type error.

The issue's own program used the library function `Browser.sandbox`; this version reproduces the
same bug with a local `sandbox` of the same type, built on `Platform.worker`, in its place.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, s-atpat-record
-- COMPILE-ERROR: field iDontExist does not exist
-- CHECK: {{-- [A-Z ]+ -}}
-- CHECK-NOT: out of bounds

import Html


sandbox :
    { init : model
    , view : model -> Html.Html msg
    , update : msg -> model -> model
    }
    -> Program () model msg
sandbox app =
    Platform.worker
        { init = \_ -> ( app.init, Cmd.none )
        , update = \msg model -> ( app.update msg model, Cmd.none )
        , subscriptions = \_ -> Sub.none
        }


main : Program () { window : Int } msg
main =
    sandbox
        { init = { window = 1 }
        , view = view
        , update = \_ model -> model
        }


foo : Float
foo =
    0


bar : { window : Int } -> Float
bar model =
    1


view ({ iDontExist } as model) =
    let
        _ =
            foo iDontExist <| bar model
    in
    Html.text ""
