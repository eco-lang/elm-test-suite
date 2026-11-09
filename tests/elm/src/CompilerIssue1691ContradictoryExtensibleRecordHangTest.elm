module CompilerIssue1691ContradictoryExtensibleRecordHangTest exposing (main)

{-| A point-free definition whose extensible-record annotations contradict each other is rejected with a type error.

<https://github.com/elm/compiler/issues/1691>

`combineAB` passes `Just` where `combineMaybeAB` needs a function from `PartialRecordA a` to
`Maybe (PartialRecordB a)`, which would make `a` contain itself.

Elm 0.19.1 hangs on it, its memory growing without bound, instead of reporting the error.

The issue's own program used the library function `Maybe.map` in `fullRecord`; this version
reproduces the same bug with a `case` on the `Maybe` in its place.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, s-exp-app, s-valbind-var
-- COMPILE-ERROR: a type error, not a hang
-- CHECK: {{-- [A-Z ]+ -}}
-- CHECK-NOT: HasCallStack

import Html


type alias FullRecord =
    { fieldA : String
    , fieldB : Maybe String
    }


type alias PartialRecordA a =
    { a | fieldA : String }


type alias PartialRecordB a =
    { a | fieldB : String }


fullRecord : PartialRecordA a -> Maybe (PartialRecordB b) -> FullRecord
fullRecord partialRecordA partialRecordB =
    { fieldA = partialRecordA.fieldA
    , fieldB =
        case partialRecordB of
            Just r ->
                Just r.fieldB

            Nothing ->
                Nothing
    }


combineA : PartialRecordA a -> FullRecord
combineA =
    combineMaybeAB (always Nothing)


combineAB : PartialRecordA (PartialRecordB a) -> FullRecord
combineAB =
    combineMaybeAB Just


combineMaybeAB : (PartialRecordA a -> Maybe (PartialRecordB a)) -> PartialRecordA a -> FullRecord
combineMaybeAB partialSelectorB partialRecordA =
    fullRecord partialRecordA (partialSelectorB partialRecordA)


main =
    Html.text ""
