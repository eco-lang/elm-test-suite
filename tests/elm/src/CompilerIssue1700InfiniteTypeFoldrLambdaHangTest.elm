module CompilerIssue1700InfiniteTypeFoldrLambdaHangTest exposing (main)

{-| A `foldr` lambda that conses a list onto an element (`uniq :: elem`) is rejected with an infinite-type error.

<https://github.com/elm/compiler/issues/1700>

Elm 0.19.1 hangs on it, its memory growing without bound, instead of reporting the error.

The issue's own program used the library functions `List.foldr` and `List.member`; this version
reproduces the same bug with local `foldr` and `member` of the same types in their place.

-}

-- TAGS: elm19-bug
-- TAGS: elm-spec, s-exp-app, s-atexp-op
-- COMPILE-ERROR: a type error, not a hang
-- CHECK: {{-- [A-Z ]+ -}}
-- CHECK-NOT: HasCallStack

import Html


foldr : (a -> b -> b) -> b -> List a -> b
foldr f acc list =
    case list of
        [] ->
            acc

        x :: rest ->
            f x (foldr f acc rest)


member : a -> List a -> Bool
member x list =
    case list of
        [] ->
            False

        y :: rest ->
            x == y || member x rest


listUnique : List a -> List a
listUnique lst =
    foldr
        (\elem uniq ->
            if member elem uniq then
                uniq

            else
                uniq :: elem
        )
        []
        lst


main =
    Html.text ""
