module StringEscapeCrTest exposing (main)

{-| The `\r` escape in a string literal is a carriage return, code point 13.

Each check compares a string with the same string spelled with `\u{...}`
escapes only, which give the code points directly:

  - `"\r"` alone;
  - `\r` among the other escapes `\n`, `\t`, `\\` and `\"`, ordinary letters,
    and `\u{000D}`;
  - `"\r\n"`, which is the two characters 13 and 10;
  - `\r` inside a triple-quoted string.

It also checks that the string `"\u{000D}"` matches the `"\r"` pattern in a
`case`.

-}

-- TAGS: elm-spec, d-atexp-scon, d-atpat-scon
-- CHECK: cr: True
-- CHECK: mixed: True
-- CHECK: crlf: True
-- CHECK: triple: True
-- CHECK: pattern: "carriage return"

import Html exposing (text)


describe : String -> String
describe s =
    case s of
        "\r" ->
            "carriage return"

        "\n" ->
            "newline"

        _ ->
            "other"


main =
    let
        _ =
            Debug.log "cr" ("\r" == "\u{000D}")

        _ =
            Debug.log "mixed" ("a\rb\nc\td\\e\"f\u{000D}g" == "\u{0061}\u{000D}\u{0062}\u{000A}\u{0063}\u{0009}\u{0064}\u{005C}\u{0065}\u{0022}\u{0066}\u{000D}\u{0067}")

        _ =
            Debug.log "crlf" ("\r\n" == "\u{000D}\u{000A}")

        _ =
            Debug.log "triple" ("""x\ry""" == "\u{0078}\u{000D}\u{0079}")

        _ =
            Debug.log "pattern" (describe "\u{000D}")
    in
    text "done"
