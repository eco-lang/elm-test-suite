module Regions exposing (replace)

{-| Replacing the generated region of a file: the lines between a line starting with `begin` and the
next line starting with `end` (both marker lines are kept). It is an error if either marker is
missing or occurs more than once.
-}


replace : { begin : String, end : String } -> String -> String -> Result String String
replace markers body source =
    let
        lines =
            String.lines source

        indexed =
            List.indexedMap Tuple.pair lines

        at prefix =
            List.filter (\( _, l ) -> String.startsWith prefix l) indexed |> List.map Tuple.first
    in
    case ( at markers.begin, at markers.end ) of
        ( [ b ], [ e ] ) ->
            if e > b then
                Ok
                    (String.join "\n"
                        (List.take (b + 1) lines ++ [ body ] ++ List.drop e lines)
                    )

            else
                Err ("the marker '" ++ markers.end ++ "' comes before '" ++ markers.begin ++ "'")

        ( bs, es ) ->
            Err
                ("expected one line starting '"
                    ++ markers.begin
                    ++ "' and one starting '"
                    ++ markers.end
                    ++ "', found "
                    ++ String.fromInt (List.length bs)
                    ++ " and "
                    ++ String.fromInt (List.length es)
                )
