module CompilerIssue2185PhantomWrapperLetAnnotationTest exposing (main)

{-| A valid `let` annotation with a type variable around a wrapped phantom type compiles and runs.

<https://github.com/elm/compiler/issues/2185>

`func` (unannotated) has type `Internal a -> Bool`; its `let` annotation `x : Wrapper a` is fine.
Elm 0.19.1 crashes ("You ran into a compiler bug ... a [rank = 2]", Type/Solve.hs:206, then
"thread blocked indefinitely in an MVar operation"). It should compile.

A Standard Definition of Elm? does not accept this as a bug. `func` is unannotated, so the `a` of
the annotation `x : Wrapper a` is a variable of that annotation alone, and `x` must have exactly
the type `Wrapper a` with `a` uninstantiated (rule s-valbind-var). Its value `Wrapper internal`
has the type `Wrapper b`, where `b` is the type of `func`'s argument: the annotation is more
general than the value, or `a` would escape it. The program is rejected; that Elm 0.19.1 crashes
instead of reporting an error is a bug, but not the one this test expects to see fixed.
<https://elm-test-suite.netlify.app/standard/rules/s-valbind-var>

-}

-- TAGS: elm19-bug, elm-spec-contradicts
-- XFAIL: the book rejects the program: the annotation x : Wrapper a is more general than its value
-- CHECK: func: True

import Html exposing (text)


type Wrapper a
    = Wrapper (Internal a)


type Internal a
    = Internal


func internal =
    let
        x : Wrapper a
        x =
            Wrapper internal
    in
    True


main =
    let
        _ =
            Debug.log "func" (func Internal)
    in
    text "done"
