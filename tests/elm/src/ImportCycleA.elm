module ImportCycleA exposing (a)

{-| Half of an import cycle, for ImportCycleTest. -}

-- HELPER: imported by ImportCycleTest; imports ImportCycleB, which imports it

import ImportCycleB


a : Int
a =
    1


b : Int
b =
    ImportCycleB.b
