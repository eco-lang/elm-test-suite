module CompilerIssue1947MultilineStringInLetBinopTest exposing (..)

{-| A multi-line string whose closing quotes are left of the `let` body cannot be followed by an operator.

<https://github.com/elm/compiler/issues/1947>

The closing `"""` of a multi-line string in a let binding sits in column 1, and Elm 0.19.1
rejects the `++` that follows it with a parse error. The program is valid; it should compile and
log the string, a newline followed by `!`.

A Standard Definition of Elm? does not accept this as a bug. Under the layout rule every item of
a phrase is indented, and only the column at which an item begins counts (restriction
core-layout-rule): the `++` begins in column 5, left of the column of `someString`, under which
the definitions of the `let` are read, so it cannot continue the definition, and the program is
rejected, as Elm 0.19.1 rejects it.
<https://elm-test-suite.netlify.app/standard/restrictions/core-layout-rule>

-}

-- TAGS: elm19-bug, elm-spec-contradicts
-- XFAIL: under the layout rule the ++ begins left of the let definitions, so the program is rejected
-- CHECK: someString: "\n!"

import Html exposing (text)


main =
    let
        someString =
            """
""" ++ "!"

        _ =
            Debug.log "someString" someString
    in
    text "done"
