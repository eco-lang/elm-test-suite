module LetNumberContainerDualTest exposing (main)

{-| One unannotated `let`-bound tuple of number literals is used both as Ints and as
Floats.

Elm generalises the binding `t = ( 30, 40 )`, so `Tuple.first t + 1` uses it at
`Int` (31) and `Tuple.first t * 1.5` uses it at `Float` (rounded, 45). The annotation
`intUse : Int` fixes the first use at Int; without it, nothing would fix that use, and A Standard
Definition of Elm? would take it to be Float (ruling A27).

-}

-- TAGS: elm-spec, s-dec-group, s-atexp-longvar, sec:dynamic-core-numbers, d-atexp-scon
-- CHECK: dual-int: 31
-- CHECK: dual-float: 45

import Html exposing (text)


main =
    let
        t =
            ( 30, 40 )

        intUse : Int
        intUse =
            Tuple.first t + 1

        floatUse =
            round (Tuple.first t * 1.5)

        _ =
            Debug.log "dual-int" intUse

        _ =
            Debug.log "dual-float" floatUse
    in
    text "done"
