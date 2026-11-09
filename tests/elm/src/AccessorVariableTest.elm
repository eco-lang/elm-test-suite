module AccessorVariableTest exposing (main)

{-| A record accessor works when bound to a variable, and `.name` works on elements of lists of two different record types.

The elements are taken out of the lists by pattern matching, and `.value` is applied to each
element of a list of three records.

-}

-- TAGS: elm-spec, s-atpat-record, d-patrow-field
-- CHECK: via_var: 42
-- CHECK: mapped: [10,20,30]
-- CHECK: person_name: "Alice"
-- CHECK: company_name: "ACME"

import Html exposing (text)


main =
    let
        accessor = .value
        item = { value = 42, label = "test" }
        _ = Debug.log "via_var" (accessor item)
        items = [ { value = 10 }, { value = 20 }, { value = 30 } ]
        mapped =
            case items of
                [ i1, i2, i3 ] ->
                    [ .value i1, .value i2, .value i3 ]

                _ ->
                    []
        _ = Debug.log "mapped" mapped
        persons = [ { name = "Alice", age = 30 } ]
        companies = [ { name = "ACME", employees = 100 } ]
        personName =
            case persons of
                p :: _ ->
                    .name p

                [] ->
                    "none"
        companyName =
            case companies of
                c :: _ ->
                    .name c

                [] ->
                    "none"
        _ = Debug.log "person_name" personName
        _ = Debug.log "company_name" companyName
    in
    text "done"
