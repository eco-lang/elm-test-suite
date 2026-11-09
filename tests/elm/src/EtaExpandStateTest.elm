module EtaExpandStateTest exposing (main)

{-| A state monad over the function alias `St a = Int -> ( Int, a )`, with `sequence` written recursively using `andThen` and `pure`, threads its state correctly.

`andThen`, `pure`, `tick` and `tick2` are annotated against `St` and take the state as an extra parameter in their definitions. `sequence` is written without the state parameter: each branch returns a `St` value built by partial application.

`run n` sequences `[ tick, tick2, pure 5, tick ]` from state `n`, which yields `n`, `10 * (n + 1)`, `5` and `n + 3`, and sums them to `12 * n + 18` with a local `sum`. For `n` equal to 1, 2 and 3 that is `[30,42,54]`; a mistake in how the state is threaded changes these numbers.
-}

import Html exposing (text)



-- TAGS: elm-spec, sm-typbind, s-ty-con, s-valbind-var, d-app-closure, d-valbind-pat
-- CHECK: r: [30,42,54]


type alias St a =
    Int -> ( Int, a )


andThen : (a -> St b) -> St a -> St b
andThen f ma s0 =
    let
        ( s1, a ) =
            ma s0
    in
    f a s1


pure : a -> St a
pure x s =
    ( s, x )


tick : St Int
tick s =
    ( s + 1, s )


tick2 : St Int
tick2 s =
    ( s + 2, s * 10 )


sequence : List (St a) -> St (List a)
sequence actions =
    case actions of
        [] ->
            pure []

        m :: rest ->
            m |> andThen (\x -> sequence rest |> andThen (\xs -> pure (x :: xs)))


sum : List Int -> Int
sum xs =
    case xs of
        [] ->
            0

        x :: rest ->
            x + sum rest


run : Int -> Int
run n =
    let
        ( _, xs ) =
            sequence [ tick, tick2, pure 5, tick ] n
    in
    sum xs


main =
    let
        _ =
            Debug.log "r" [ run 1, run 2, run 3 ]
    in
    text "done"
