module ImportCycleB exposing (b)

{-| Half of an import cycle, for ImportCycleTest. -}

-- HELPER: imported by ImportCycleA, which it imports

import ImportCycleA


b : Int
b =
    ImportCycleA.a + 1
