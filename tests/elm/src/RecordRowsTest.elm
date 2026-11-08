module RecordRowsTest exposing (main)

{-| Record expressions, record types and record patterns are rows of fields.

A Standard Definition of Elm?, rules s-exprow (a record expression's fields, each typed by its
expression), s-tyrow (a record type's fields), s-patrow (a record pattern's field binds the
variable spelt as its label) and s-ty-unit (the type `()`). The record alias `Point` declares a
constructor taking the fields in the order written (rule dm-topdec-alias). <https://elm-test-suite.netlify.app/standard/rules/s-patrow>

-}

-- TAGS: elm-spec, s-exprow, s-tyrow, s-patrow, s-ty-unit, dm-topdec-alias, sm-typbind-record
-- CHECK: sum of fields: 3
-- CHECK: label: "p"
-- CHECK: constructor order: (1,2)
-- CHECK: unit: 5

import Html


type alias Point =
    { y : Int, x : Int }


sumFields : { x : Int, y : Int, label : String } -> Int
sumFields { x, y } =
    x + y


labelOf : { x : Int, y : Int, label : String } -> String
labelOf { label } =
    label


five : () -> Int
five () =
    5


main =
    let
        r =
            { x = 1, y = 2, label = "p" }

        _ =
            Debug.log "sum of fields" (sumFields r)

        _ =
            Debug.log "label" (labelOf r)

        _ =
            Debug.log "constructor order" (let p = Point 1 2 in ( p.y, p.x ))

        _ =
            Debug.log "unit" (five ())
    in
    Html.text "done"
