module ImportExposingAllTest exposing (main)

{-| `exposing (..)` in an import brings in everything the imported module exposes.

A Standard Definition of Elm?, rule dm-explist-all: the exposing list `(..)` gives every value the
module's interface holds. `double`, `exposedCount`, the constructors of `Open` and the record
constructor `Point` are all used unqualified. <https://elm-test-suite.netlify.app/standard/rules/dm-explist-all>

-}

-- TAGS: elm-spec, dm-explist-all
-- CHECK: all: [42,101,7,3]

import Html
import ModuleExposingHelper exposing (..)


main =
    let
        two =
            case Two 7 of
                Two n ->
                    n

                One ->
                    0

        point =
            Point 1 2
    in
    let
        _ =
            Debug.log "all" [ double 21, exposedCount, two, point.x + point.y ]
    in
    Html.text "done"
