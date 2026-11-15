module WideRecordGcBitmapTest exposing (main)

{-| A 17-field record holding one `Int` and sixteen `String`s keeps its field
values while the program builds large lists before reading them.

`w1` is built with a `count` of 50000 (the length of one list), then a list of
150000 strings is built before `w2` is made and both are read. The test checks
that the two counts add to 200000 and that `w1.p ++ w2.a` is `"pa"`. A local
`length` counts the lists.

A Standard Definition of Elm? places no bound on the resources evaluation uses, and an
implementation that stops for lack of them is outside the definition (Appendix,
Implementation-Dependent Details, Resource Limits). The book's result for this program is the one
the test expects, but a compiler that runs out of stack or memory on it does not contradict the
book, so the test is tagged `elm-unspecced`: it checks an implementation's resources.

<https://elm-test-suite.netlify.app/standard/appendix-implementation#sec-appendix-implementation-limits>

-}

-- TAGS: elm-unspecced
-- CHECK: WideRecordGcBitmap: 200000
-- CHECK: WideRecordGcBitmapTag: "pa"

import Html exposing (text)


type alias Wide =
    { count : Int
    , a : String
    , b : String
    , c : String
    , d : String
    , e : String
    , f : String
    , g : String
    , h : String
    , i : String
    , j : String
    , k : String
    , l : String
    , m : String
    , n : String
    , o : String
    , p : String
    }


mkWide : Int -> Wide
mkWide count =
    { count = count
    , a = "a"
    , b = "b"
    , c = "c"
    , d = "d"
    , e = "e"
    , f = "f"
    , g = "g"
    , h = "h"
    , i = "i"
    , j = "j"
    , k = "k"
    , l = "l"
    , m = "m"
    , n = "n"
    , o = "o"
    , p = "p"
    }


churn : Int -> List String -> List String
churn n acc =
    if n <= 0 then
        acc

    else
        churn (n - 1) (("x" ++ "y") :: acc)


length : Int -> List a -> Int
length acc xs =
    case xs of
        [] ->
            acc

        _ :: rest ->
            length (acc + 1) rest


main =
    let
        seed =
            churn 50000 []

        -- The count comes from a list length rather than a literal.
        w1 =
            mkWide (length 0 seed)

        more =
            churn 150000 []

        w2 =
            mkWide (length 0 more)

        total =
            w1.count + w2.count

        tag =
            w1.p ++ w2.a

        _ =
            Debug.log "WideRecordGcBitmap" total

        _ =
            Debug.log "WideRecordGcBitmapTag" tag
    in
    text "done"
