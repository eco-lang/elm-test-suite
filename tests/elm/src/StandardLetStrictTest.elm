module StandardLetStrictTest exposing (main)

{-| A `let` evaluates its declarations before its body, even a declaration whose value is not used:
`let _ = Debug.todo "x" in 1` has no value, so the program stops there.

A Standard Definition of Elm?, the Comment on rule r:d-atexp-let. The program logs `before`, then
stops at `Debug.todo`; `let strict` is never logged, and the program exits with status 1.
<https://elm-test-suite.netlify.app/standard/rules/d-atexp-let>

-}

-- TAGS: elm-spec, d-atexp-let
-- EXIT: 1
-- CHECK: before: ()
-- CHECK-NOT: let strict:

import Html


main =
    let
        _ =
            Debug.log "before" ()

        _ =
            Debug.log "let strict"
                (let
                    _ =
                        Debug.todo "x"
                 in
                 1
                )
    in
    Html.text "done"
