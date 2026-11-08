module ImportOperatorItemTest exposing (main)

{-| Importing an operator by name checks that the module has it, and binds nothing new.

A Standard Definition of Elm?, rules sm-item-op and dm-expitem-op: `import Basics exposing ((+),
(//))` is accepted, and `+` and `//` keep the meaning the operator table gives them.
<https://elm-test-suite.netlify.app/standard/rules/sm-item-op>

-}

-- TAGS: elm-spec, sm-item-op, dm-expitem-op
-- CHECK: sum: 7
-- CHECK: quotient: 3

import Basics exposing ((+), (//))
import Html


main =
    let
        _ =
            Debug.log "sum" (3 + 4)

        _ =
            Debug.log "quotient" (7 // 2)
    in
    Html.text "done"
