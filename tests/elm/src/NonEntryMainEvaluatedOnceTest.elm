module NonEntryMainEvaluatedOnceTest exposing (main)

{-| A top-level `main` of an imported, non-entry module is an ordinary
top-level value and is evaluated once, like any other: its `Debug.log` prints
a single line however many times it is referenced.

The test references `NonEntryMainAux.main` twice in a list and logs the
list's length, counted by a local `length`, so `auxMain` must appear once, before `uses: 2`. The CHECK-NOT
rejects a second `auxMain` line, which the CHECK-NEXT pair alone would accept.

Tagged `elm-unspecced`: A Standard Definition of Elm? evaluates a top-level value once, but an
implementation may evaluate one again on use and still conform (ruling A59; Appendix E, Top-level
Values), and what `Debug.log` prints is outside the definition (ruling A62). The test records
what Elm 0.19.1 does.

-}

-- TAGS: elm-unspecced
-- CHECK: auxMain: "abab"
-- CHECK-NEXT: uses: 2
-- CHECK-NOT: {{auxMain[^\n]*\n[^\n]*auxMain}}

import Html exposing (text)
import NonEntryMainAux


length : List a -> Int
length xs =
    case xs of
        [] ->
            0

        _ :: rest ->
            1 + length rest


main =
    let
        _ =
            Debug.log "uses" (length [ NonEntryMainAux.main, NonEntryMainAux.main ])
    in
    text "done"
