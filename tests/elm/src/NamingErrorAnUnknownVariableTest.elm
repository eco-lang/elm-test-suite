module NamingErrorAnUnknownVariableTest exposing (..)

{-| A reference to a variable that is defined nowhere, `undefinedName`, is rejected with a NAMING ERROR.

-}

-- TAGS: elm19-compile-error
-- COMPILE-ERROR: NAMING ERROR, an unknown variable
-- CHECK: -- NAMING ERROR -

testValue =
    undefinedName + 1
