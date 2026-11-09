module ImportTypeByNameLaterReplacesTest exposing (main)

{-| When two imports expose a type of the same name by name, the later import's type is the one
the name denotes: the name is not ambiguous.

`ImportTypeByNameFirstHelper` and `ImportTypeByNameSecondHelper` both expose a type `Thing`, of
different shapes. The second import comes last, so `Thing` is its `Thing`, and `x : Thing` with
the second helper's constructor compiles.

A Standard Definition of Elm?, rules sm-imports-import and sm-item-type: the imports are read from
left to right, and a type listed by name replaces any type of that name provided by an earlier
import. (Values exposed by two imports are ambiguous instead; types listed by name are not.)
<https://elm-test-suite.netlify.app/standard/rules/sm-item-type>

-}

-- TAGS: elm-spec, sm-item-type, sm-imports-import
-- CHECK: x: 7

import Html
import ImportTypeByNameFirstHelper exposing (Thing)
import ImportTypeByNameSecondHelper exposing (Thing)


x : Thing
x =
    ImportTypeByNameSecondHelper.Second 7


main =
    let
        n =
            case x of
                ImportTypeByNameSecondHelper.Second k ->
                    k

        _ =
            Debug.log "x" n
    in
    Html.text "done"
