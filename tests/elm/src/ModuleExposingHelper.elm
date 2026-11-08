module ModuleExposingHelper exposing (Closed, Open(..), Point, Shape, double, exposedCount, makeClosed, makeShape, unwrapClosed, unwrapShape)

{-| A module whose header exposes a chosen part of it, for the tests of exposing and importing:
ImportExposingItemsTest, ImportExposingAllTest, ImportUnexposedValueTest,
ImportClosedTypeConstructorTest, ImportClosedTypeOpenItemTest and ImportAliasOpenItemTest.

`Closed` and `Shape` are exposed without their constructors (`Shape`'s constructor is spelt as the
type), `Open` with them, and the record alias `Point` by name. `hidden` is not exposed.

-}

-- HELPER: imported by the Import*Test tests of exposing lists


type Closed
    = Closed Int


type Open
    = One
    | Two Int


type Shape
    = Shape Int


type alias Point =
    { x : Int, y : Int }


hidden : Int
hidden =
    100


double : Int -> Int
double n =
    2 * n


exposedCount : Int
exposedCount =
    hidden + 1


makeClosed : Int -> Closed
makeClosed n =
    Closed n


unwrapClosed : Closed -> Int
unwrapClosed (Closed n) =
    n


makeShape : Int -> Shape
makeShape n =
    Shape n


unwrapShape : Shape -> Int
unwrapShape (Shape n) =
    n
