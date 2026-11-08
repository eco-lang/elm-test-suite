module AnnotationNotFollowedByDefinitionTest exposing (main)

{-| An annotation must be followed directly by the definition it annotates.

A Standard Definition of Elm?, restriction core-annotation-placement: in source text each
annotation `x : t` is followed directly by a definition of the same `x`. Here the annotation of
`f` is followed by the definition of `g`. <https://elm-test-suite.netlify.app/standard/restrictions/core-annotation-placement>

-}

-- TAGS: elm-spec, core-annotation-placement
-- COMPILE-ERROR: an annotation separated from its definition
-- CHECK: {{-- [A-Z ]+ -}}

import Html


f : Int
g =
    2


f =
    1


main =
    Html.text (String.fromInt (f + g))
