module StandardCoreEvaluationExamplesTest exposing (main)

{-| Small programs for rules of the dynamic semantics of the Core that other tests reach only in
passing, and examples from the Comments of A Standard Definition of Elm?, Chapter 6.

  - an as-pattern around a cons pattern with a wildcard (r:d-pat-as, r:d-pat-cons);
  - the unit pattern and the unit expression (r:d-atpat-unit, r:d-atexp-unit);
  - an operator used as a value, applied fully and partially (r:d-atexp-op,
    r:d-app-basic-partial), and a constructor awaiting arguments (r:d-app-con);
  - `(&&)` as a value takes both arguments as values (the Comment on r:d-atexp-op);
  - `|>`, whose text is in the dynamic basis;
  - a case rule that fails is not evaluated, so its `Debug.todo` is not reached (r:d-mrule-fail);
  - `Just 1`, a constructor applied to its argument (r:d-app-con);
  - `1` at Float after number specialisation (r:d-atexp-scon, ruling A87);
  - `modBy` and `remainderBy` with a negative dividend, the book's examples;
  - record equality does not depend on the order fields are written in;
  - strings compared in order, and the field accessor `.k` (r:d-atpat-record, r:d-patrow-field).

<https://elm-test-suite.netlify.app/standard/dynamic-core>

-}

-- TAGS: elm-spec, d-pat-as, d-pat-cons, d-atpat-unit, d-atexp-unit, d-atexp-op, d-app-basic-partial, d-app-con, d-mrule-fail, d-atexp-scon, d-atpat-record, d-patrow-field, b:Basics.apR, b:Basics.modBy, b:Basics.remainderBy, b:Basics.compare, df:field-accessor
-- CHECK: as-pattern: (1,[1,2])
-- CHECK: unit pattern: 5
-- CHECK: operator value: 3
-- CHECK: partial basic value: <function>
-- CHECK: partial constructor: <function>
-- CHECK: (&&) is strict: False
-- CHECK: pipe: 6
-- CHECK: mrule-fail: 2
-- CHECK: Just 1: Just 1
-- CHECK: inc 0.5: 1.5
-- CHECK: modBy 4 -5: 3
-- CHECK: remainderBy 4 -5: -1
-- CHECK: record field order: True
-- CHECK: compare strings: LT
-- CHECK: accessor: 7

import Html


type Tree
    = Leaf
    | Node Tree Int Tree


add1 : Int -> Int
add1 n =
    n + 1


main =
    let
        _ =
            Debug.log "as-pattern"
                (case [ 1, 2 ] of
                    ((x :: _) as whole) ->
                        ( x, whole )

                    _ ->
                        ( 0, [] )
                )

        _ =
            Debug.log "unit pattern" ((\() -> 5) ())

        _ =
            Debug.log "operator value" ((+) 1 2)

        _ =
            Debug.log "partial basic value" ((+) 1)

        _ =
            Debug.log "partial constructor" (Node Leaf)

        _ =
            Debug.log "(&&) is strict" ((&&) False True)

        _ =
            Debug.log "pipe" (5 |> add1)

        _ =
            Debug.log "mrule-fail"
                (case 1 of
                    0 ->
                        Debug.todo "x"

                    _ ->
                        2
                )

        _ =
            Debug.log "Just 1" (Just 1)

        _ =
            Debug.log "inc 0.5"
                (let
                    incF n =
                        n + 1
                 in
                 incF 0.5
                )

        _ =
            Debug.log "modBy 4 -5" (modBy 4 -5)

        _ =
            Debug.log "remainderBy 4 -5" (remainderBy 4 -5)

        _ =
            Debug.log "record field order" ({ a = 1, b = 2 } == { b = 2, a = 1 })

        _ =
            Debug.log "compare strings" (compare "ab" "abc")

        _ =
            Debug.log "accessor" (.k { k = 7, j = 8 })
    in
    Html.text "done"
