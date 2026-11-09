module DeepEqualityTest exposing (main)

{-| `==` and `/=` give the exact answer on values nested more than 100 levels deep.

The fixtures are built by recursion on `n`: `nat n` is `n` applications of `S` to `Z`, `nest n
leaf` is `n` `Wrap`s around `Leaf leaf`, and `chain n bottom` is `n` records linked through
`next = Just ...`, ending in one whose `v` is `bottom`.

  - `nat 150 vs 200`: two naturals of different depth are not equal.
  - `nat 150 vs 150`: two naturals of the same depth are equal.
  - `nest 120` and `nest 500 /=`: values that differ only in the leaf, 120 and 500 levels down,
    are not equal.
  - `record chain 300`: record chains that differ only in the innermost `v` are not equal.

Two Dicts that differ deep down are checked by DictDeepEqualityTest.
-}

-- TAGS: elm-spec, b:Basics.eq, b:Basics.neq
-- MODE-GUARD: a Char equality must give the same answer as under --optimize
-- NO-SKIP: an edge case every compiler must run
-- CHECK: nat 150 vs 200: "False"
-- CHECK: nat 150 vs 150: "True"
-- CHECK: nest 120: "False"
-- CHECK: nest 500 /=: "True"
-- CHECK: record chain 300: "False"

import Html exposing (text)


type Nat
    = Z
    | S Nat


nat : Int -> Nat
nat n =
    if n <= 0 then
        Z

    else
        S (nat (n - 1))


type Nest
    = Leaf Int
    | Wrap Nest


nest : Int -> Int -> Nest
nest n leaf =
    if n <= 0 then
        Leaf leaf

    else
        Wrap (nest (n - 1) leaf)


type Chain
    = Chain { next : Maybe Chain, v : Int }


chain : Int -> Int -> Chain
chain n bottom =
    if n <= 0 then
        Chain { next = Nothing, v = bottom }

    else
        Chain { next = Just (chain (n - 1) bottom), v = 0 }


bool : Bool -> String
bool b =
    if b then
        "True"

    else
        "False"


main =
    let
        _ =
            Debug.log "nat 150 vs 200" (bool (nat 150 == nat 200))

        _ =
            Debug.log "nat 150 vs 150" (bool (nat 150 == nat 150))

        _ =
            Debug.log "nest 120" (bool (nest 120 1 == nest 120 2))

        _ =
            Debug.log "nest 500 /=" (bool (nest 500 1 /= nest 500 2))

        _ =
            Debug.log "record chain 300" (bool (chain 300 1 == chain 300 2))
    in
    text "done"
