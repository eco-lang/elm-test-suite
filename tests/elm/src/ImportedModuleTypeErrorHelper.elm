module ImportedModuleTypeErrorHelper exposing (value)

{-| A module with a type error, for ImportedModuleTypeErrorTest. -}

-- HELPER: imported by ImportedModuleTypeErrorTest; it does not compile, on purpose


value : Int
value =
    1 + "one"
