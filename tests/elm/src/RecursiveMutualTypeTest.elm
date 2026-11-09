module RecursiveMutualTypeTest exposing (main)

{-| A pair of mutually recursive custom types, `Forest` and `RoseTree`, can be built and traversed.

`countNodes` counts a tree of four `RoseNode`s nested up to three levels, with
`countForest`, defined with it by mutual recursion, counting each node's list of
children.
-}

-- TAGS: elm-spec, sm-topdec-types, sm-datbind, d-pat-con
-- CHECK: nodes: 4

import Html exposing (text)


type Forest a
    = Forest (List (RoseTree a))


type RoseTree a
    = RoseNode a (Forest a)


countNodes : RoseTree a -> Int
countNodes (RoseNode _ (Forest children)) =
    1 + countForest children


countForest : List (RoseTree a) -> Int
countForest trees =
    case trees of
        [] ->
            0

        tree :: rest ->
            countNodes tree + countForest rest


main =
    let
        tree = RoseNode 1 (Forest
            [ RoseNode 2 (Forest [])
            , RoseNode 3 (Forest [ RoseNode 4 (Forest []) ])
            ])
        _ = Debug.log "nodes" (countNodes tree)
    in
    text "done"
