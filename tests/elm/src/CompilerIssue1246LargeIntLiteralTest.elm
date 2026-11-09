module CompilerIssue1246LargeIntLiteralTest exposing (main)

{-| Int literals that do not fit 64 bits are silently wrapped.

<https://github.com/elm/compiler/issues/1246>

Elm 0.19.1 reads integer literals into a 64-bit Int, so `100000000000000000000` becomes
7766279631452242000 and 2^63 becomes -2^63, with no error. The literal should keep its value
(as a JavaScript number); silently changing it is wrong.

A Standard Definition of Elm? does not decide this test. An integer constant spelling n denotes
norm(n), and the Int range and the normalisation norm are implementation parameters (Appendix,
The Int Range and Normalisation): the range must hold every integer from -2^31 to 2^31 - 1, and may
hold more. An implementation whose Int range holds `100000000000000000000` and 2^63 keeps both
literals as they are written; one with a 64-bit range wraps them, as eco does, and conforms too.

The test is marked XFAIL because these numbers are too large for every current implementation:
none has an Int range that holds them, so every compiler changes them and the test fails. It is
not a bug against the book. Review it when there is an Elm with built-in large integers, whose
Int range would hold them and on which the test should pass.

<https://elm-test-suite.netlify.app/standard/appendix-implementation#sec-appendix-implementation-int>

-}

-- TAGS: elm19-bug, elm-unspecced
-- XFAIL: the numbers are too large for the Int range of every current implementation; review when an Elm has built-in large integers
-- CHECK: big: 100000000000000000000
-- CHECK: sixtyThree: 9223372036854776000

import Html exposing (text)


big : Int
big =
    100000000000000000000


sixtyThree : Int
sixtyThree =
    9223372036854775808


main =
    let
        _ =
            Debug.log "big" big

        _ =
            Debug.log "sixtyThree" sixtyThree
    in
    text "done"
