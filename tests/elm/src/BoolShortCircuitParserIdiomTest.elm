module BoolShortCircuitParserIdiomTest exposing (main)

{-| A bounds check guarding an indexing call with `&&` (`idx < length src && unsafeIndex src idx /= ...`) stops the call from running past the end of the input.

`&&` must not evaluate its right operand when the left is `False`. The input
is a list of characters, and `length` and `drop` are local functions written
by pattern matching. The right operand would reach a branch that recurses
without end, so a past-end peek must print `"none"`, and an in-bounds peek
prints the character.
-}

-- TAGS: elm-spec, d-exp-case, d-mrule-fail
-- CHECK: peek at past-end: "none"
-- CHECK: peek at first: 'H'

import Html exposing (text)


{-| Recurses without end; never called when the program is correct.
-}
stackBomb : Int -> Int
stackBomb n =
    1 + stackBomb (n + 1)


{-| The number of elements of a list.
-}
length : List a -> Int
length xs =
    case xs of
        [] ->
            0

        _ :: rest ->
            1 + length rest


{-| The list without its first `n` elements.
-}
drop : Int -> List a -> List a
drop n xs =
    if n <= 0 then
        xs

    else
        case xs of
            [] ->
                []

            _ :: rest ->
                drop (n - 1) rest


{-| Returns the character at `index`, or calls `stackBomb` when `index` is past the end.
-}
unsafeIndex : List Char -> Int -> Char
unsafeIndex chars index =
    case drop index chars of
        c :: _ ->
            c

        [] ->
            -- Unreachable under correct short-circuit semantics.
            if stackBomb 0 == 0 then
                '?'

            else
                '?'


{-| Returns the character at `idx`, or `Nothing` when `idx` is past the end.
-}
peek : List Char -> Int -> Maybe Char
peek src idx =
    if idx < length src && unsafeIndex src idx /= '\u{0000}' then
        Just (unsafeIndex src idx)

    else
        Nothing


main =
    let
        pastEnd : String
        pastEnd =
            case peek [ 'H', 'i' ] 2 of
                Just c ->
                    "CHAR:" ++ Debug.toString c

                Nothing ->
                    "none"

        first : Char
        first =
            case peek [ 'H', 'i' ] 0 of
                Just c ->
                    c

                Nothing ->
                    '?'

        _ =
            Debug.log "peek at past-end" pastEnd

        _ =
            Debug.log "peek at first" first
    in
    text "done"
