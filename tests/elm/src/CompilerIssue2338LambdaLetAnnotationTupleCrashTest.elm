module CompilerIssue2338LambdaLetAnnotationTupleCrashTest exposing (main)

{-| The compiler reports a TYPE MISMATCH for a let annotation `( Int, x )` inside a lambda passed to a higher-order function.

<https://github.com/elm/compiler/issues/2338>

`return : ( Int, x )` claims the second component can be any type, but it is `b`, an argument of
the lambda passed to `mapAccuml`. Elm 0.19.1 crashes instead ("x [rank = 2]", Type/Solve.hs:206,
"thread blocked indefinitely in an MVar operation").

The issue's own program used the library functions `List.foldl` and `List.reverse` to define
`mapAccuml`; this version reproduces the same bug with `mapAccuml` defined by direct recursion on
the list instead.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, s-valbind-var
-- COMPILE-ERROR: TYPE MISMATCH, not a compiler crash
-- CHECK-NOT: HasCallStack
-- CHECK: -- TYPE MISMATCH -

import Html exposing (text)


main =
    text "done"


mapAccuml : (a -> b -> ( a, c )) -> a -> List b -> ( a, List c )
mapAccuml f acc0 list =
    case list of
        [] ->
            ( acc0, [] )

        x :: rest ->
            let
                ( acc1, y ) =
                    f acc0 x

                ( accFinal, ys ) =
                    mapAccuml f acc1 rest
            in
            ( accFinal, y :: ys )


func =
    mapAccuml
        (\a b ->
            let
                return : ( Int, x )
                return =
                    ( a, b )
            in
            return
        )
        ( 0, 0 )
