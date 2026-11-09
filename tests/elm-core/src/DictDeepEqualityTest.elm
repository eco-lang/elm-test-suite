module DictDeepEqualityTest exposing (main)

{-| `==` gives the exact answer on two Dicts whose values under one key differ 150 levels down.

`nest n leaf` is `n` `Wrap`s around `Leaf leaf`. The two Dicts hold `nest 150 1` and `nest 150 2`
under key 1, and `Leaf 0` under key 2, so they are not equal. The same depths in values of the
language are checked by DeepEqualityTest.
-}

-- MODE-GUARD: a Char equality must give the same answer as under --optimize
-- NO-SKIP: an edge case every compiler must run
-- CHECK: dict nest 150: False

import Dict
import Html exposing (text)


type Nest
    = Leaf Int
    | Wrap Nest


nest : Int -> Int -> Nest
nest n leaf =
    if n <= 0 then
        Leaf leaf

    else
        Wrap (nest (n - 1) leaf)


main =
    let
        _ =
            Debug.log "dict nest 150"
                (Dict.fromList [ ( 1, nest 150 1 ), ( 2, Leaf 0 ) ]
                    == Dict.fromList [ ( 1, nest 150 2 ), ( 2, Leaf 0 ) ]
                )
    in
    text "done"
