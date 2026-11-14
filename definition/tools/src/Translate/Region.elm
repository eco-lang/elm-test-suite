module Translate.Region exposing (Position, Region, fromA, startText)

{-| The translator's positions in a source text (plans/eco-parser.md, E10): rows and columns from 1,
columns counted in code points, the end just past the last character, as eco's parser counts them.
-}

import Compiler.Core.Annotation as A


type alias Position =
    { row : Int, column : Int }


type alias Region =
    { start : Position, end : Position }


fromA : A.Region -> Region
fromA (A.Region (A.Position r1 c1) (A.Position r2 c2)) =
    { start = { row = r1, column = c1 }, end = { row = r2, column = c2 } }


{-| "row:col" of the start, as the manifest prints a position.
-}
startText : Region -> String
startText r =
    String.fromInt r.start.row ++ ":" ++ String.fromInt r.start.column
