module ImportClosedTypeOpenItemTest exposing (main)

{-| `import M exposing (T(..))` of a type that `M` exposes closed imports the type and no
constructors.

A Standard Definition of Elm?, rules sm-item-opentype and dm-expitem-open: the item elaborates, and
imports the constructors that `M` exposes, here none. The program uses `Closed` only as a type, so
it is valid. This is the book's counterpart of <https://github.com/elm/compiler/issues/1979>,
whose test (`CompilerIssue1979ImportOpaqueConstructorsTest`) expects the import to be rejected.
<https://elm-test-suite.netlify.app/standard/rules/sm-item-opentype>

-}

-- TAGS: elm-spec, sm-item-opentype, dm-expitem-open
-- CHECK: closed: 9

import Html
import ModuleExposingHelper exposing (Closed(..))


roundTrip : Int -> Closed
roundTrip n =
    ModuleExposingHelper.makeClosed n


main =
    let
        _ =
            Debug.log "closed" (ModuleExposingHelper.unwrapClosed (roundTrip 9))
    in
    Html.text "done"
