module CompilerIssue1246LargeIntLiteralTest exposing (main)

{-| Int literals that do not fit 64 bits are silently wrapped.

<https://github.com/elm/compiler/issues/1246>

Elm 0.19.1 reads integer literals into a 64-bit Int, so `100000000000000000000` becomes
7766279631452242000 and 2^63 becomes -2^63, with no error. The literal should keep its value
(as a JavaScript number); silently changing it is wrong.

A Standard Definition of Elm? does not decide this test. An integer constant spelling n denotes
norm(n), and the Int range and the normalisation norm are implementation parameters (Appendix,
The Int Range and Normalisation): wrapping `100000000000000000000` into 64 bits, as Elm 0.19.1
does, is one choice the book allows, and keeping it as a JavaScript number another. The test is
marked XFAIL for that reason: it records the issue as reported, which no compiler meets.

-}

-- TAGS: elm19-bug, elm-unspecced
-- XFAIL: the book leaves the value of an integer constant outside the Int range to the implementation (norm), and every compiler wraps it
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
