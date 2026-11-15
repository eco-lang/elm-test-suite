module StandardA99RecordPatternRowPunRejectedTest exposing (..)

{-| A record pattern row written `lab = var`, with the variable spelt as the label, is rejected.

A Standard Definition of Elm?, ruling A99: `{ n = n }` is the equivalent form of `{ n }`, but a
program may write only the derived form (restriction core-pattern-row-label-only). Elm 0.19.1
reports UNFINISHED RECORD PATTERN.
<https://elm-test-suite.netlify.app/standard/restrictions/core-pattern-row-label-only>

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, core-pattern-row-label-only
-- COMPILE-ERROR: UNFINISHED RECORD PATTERN, a pattern row with `=`
-- CHECK: -- UNFINISHED RECORD PATTERN -

testValue =
    let
        { n = n } =
            { n = 1 }
    in
    n
