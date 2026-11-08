module AliasProblemQualifiedTypeTest exposing (..)

{-| A type alias that refers to itself through a qualified type is rejected with an ALIAS PROBLEM.

`A` is defined as `Maybe.Maybe (List A)`. Writing the module-qualified name
`Maybe.Maybe` does not make the recursion acceptable: a type alias cannot refer to itself.

-}

-- TAGS: elm19-compile-error
-- COMPILE-ERROR: ALIAS PROBLEM, qualified type
-- CHECK: -- ALIAS PROBLEM -

type alias A = Maybe.Maybe (List A)
