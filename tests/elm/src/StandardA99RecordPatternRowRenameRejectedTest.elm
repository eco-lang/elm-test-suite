module StandardA99RecordPatternRowRenameRejectedTest exposing (..)

{-| A record pattern row written `lab = var` is rejected.

A Standard Definition of Elm?, ruling A99: the bare pattern row `lab = var` is in the book's grammar
so that number specialisation can rename a row's variable, but no program may write it (restriction
core-pattern-row-label-only). Elm 0.19.1 reports UNFINISHED RECORD PATTERN.
<https://elm-test-suite.netlify.app/standard/restrictions/core-pattern-row-label-only>

-}

-- TAGS: elm19-compile-error
-- TAGS: elm-spec, core-pattern-row-label-only
-- COMPILE-ERROR: UNFINISHED RECORD PATTERN, a pattern row with `=`
-- CHECK: -- UNFINISHED RECORD PATTERN -

testValue =
    let
        { n = m } =
            { n = 1 }
    in
    m
