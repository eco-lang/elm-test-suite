module UnreachableBrokenHelper exposing (value)

{-| A module with a type error that no module imports, for UnreachableModuleTest. -}

-- HELPER: imported by no module, on purpose: see UnreachableModuleTest; it does not compile


value : Int
value =
    "not an Int"
