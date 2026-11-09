module StandardA53CharOrderTest exposing (main)

{-| Characters are ordered by their code points.

A Standard Definition of Elm?, ruling A53: `compare` on characters compares their codes (`toCode`).
<https://elm-test-suite.netlify.app/standard/appendix-dynamic-basis#sec-appendix-dynamic-basis-order>

`'😀'` is U+1F600 and `'ﬀ'` is U+FB00, so `'😀'` is the greater. Elm 0.19.1 compares the UTF-16
code units, where `'😀'` starts with the surrogate 0xD83D, below 0xFB00, so it puts `'😀'` first.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, b:Basics.compare, b:Basics.gt, b:Char.Char, b:Char.toCode
-- CHECK: compare '😀' 'ﬀ': GT
-- CHECK: '😀' > 'ﬀ': True
-- CHECK: toCode order agrees: True

import Html


main =
    let
        _ =
            Debug.log "compare '😀' 'ﬀ'" (compare '😀' 'ﬀ')

        _ =
            Debug.log "'😀' > 'ﬀ'" ('😀' > 'ﬀ')

        _ =
            Debug.log "toCode order agrees" (compare '😀' 'ﬀ' == compare (Char.toCode '😀') (Char.toCode 'ﬀ'))
    in
    Html.text "done"
