module ImportExposingItemsTest exposing (main)

{-| An import's exposing list brings exactly its items into scope, with what the imported module's
header exposes.

A Standard Definition of Elm?, the rules of headers, exposing lists and exposing items:
`ModuleExposingHelper`'s header exposes some of its names (rules sm-header and dm-header). The
import `exposing (Open(..), Point, Closed, double)` brings in `double` (dm-expitem-var), the
constructors of `Open` (sm-item-opentype, dm-expitem-open), the record alias `Point` with its
constructor (sm-item-type, dm-expitem-alias) and the type `Closed` without its constructor
(dm-expitem-type), all together (sm-explist-items, dm-explist-items). The other exposed values
are still reached qualified. The helper is evaluated once, before this module (dm-module).
<https://elm-test-suite.netlify.app/standard/rules/dm-expitem-alias>

-}

-- TAGS: elm-spec, sm-header, dm-header, sm-explist-items, dm-explist-items, sm-item-type, sm-item-opentype
-- TAGS: dm-expitem-var, dm-expitem-alias, dm-expitem-open, dm-expitem-type, dm-module
-- CHECK: double: 42
-- CHECK: open: [0,7]
-- CHECK: point: 3
-- CHECK: closed: 5
-- CHECK: qualified: 101

import Html
import ModuleExposingHelper exposing (Closed, Open(..), Point, double)


openValue : Open -> Int
openValue o =
    case o of
        One ->
            0

        Two n ->
            n


pointSum : Point -> Int
pointSum p =
    p.x + p.y


closedValue : Closed -> Int
closedValue c =
    ModuleExposingHelper.unwrapClosed c


main =
    let
        _ =
            Debug.log "double" (double 21)

        _ =
            Debug.log "open" (List.map openValue [ One, Two 7 ])

        _ =
            Debug.log "point" (pointSum (Point 1 2))

        _ =
            Debug.log "closed" (closedValue (ModuleExposingHelper.makeClosed 5))

        _ =
            Debug.log "qualified" ModuleExposingHelper.exposedCount
    in
    Html.text "done"
