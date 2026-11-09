module InfixAssocRightConsAppendTest exposing (main)

{-| `::` and `++` (both precedence 5) associate to the right, so `"a" ++ "b" :: [ "c" ]` does not type.

A Standard Definition of Elm?, Section 2.7 and Figure 3 (the fixities of the operators of the
initial basis): operators of equal precedence that both associate to the left group to the
left, and both to the right, to the right. <https://elm-test-suite.netlify.app/standard/figures/core-fixities>

The chain is `"a" ++ ("b" :: [ "c" ])`, which appends a list of strings to a string: a type
error. Grouped to the left it would be `("a" ++ "b") :: [ "c" ]`, `["ab","c"]`.

-}

-- TAGS: elm-spec, fig:core-fixities, df:infix, b:Basics.append, s-exp-app
-- COMPILE-ERROR: a chain that types only when grouped to the left
-- CHECK: TYPE MISMATCH

import Html


main =
    let
        _ =
            Debug.log "chain" ("a" ++ "b" :: [ "c" ])
    in
    Html.text "done"
