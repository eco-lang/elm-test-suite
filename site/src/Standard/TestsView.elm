module Standard.TestsView exposing (section)

{-| The tests that check a rule or restriction, on its page: each links to the test's page.
-}

import Data exposing (TestRef)
import Html exposing (Html)
import Html.Attributes as Attr
import Route


{-| `noun` is "rule" or "restriction".
-}
section : String -> List TestRef -> Html msg
section noun tests =
    Html.div [ Attr.class "sd-book" ]
        [ Html.section [ Attr.class "ts-section", Attr.id "tests" ]
            [ Html.h2 [ Attr.class "sd-h sd-h1" ] [ Html.text ("Tests (" ++ String.fromInt (List.length tests) ++ ")") ]
            , if List.isEmpty tests then
                Html.p [ Attr.class "ts-muted" ] [ Html.text ("No test of the suite checks this " ++ noun ++ " yet.") ]

              else
                Html.ul [ Attr.class "sd-list" ] (List.map item tests)
            ]
        ]


item : TestRef -> Html msg
item t =
    Html.li []
        [ Html.span [ Attr.class "ts-muted" ] [ Html.text (t.project ++ " / ") ]
        , Html.a
            [ Attr.class "ts-test-name"
            , Attr.href (Route.toString (Route.Projects__Project___Test_ { project = t.project, test = t.test }))
            ]
            [ Html.text t.test ]
        , if String.isEmpty t.summary then
            Html.text ""

          else
            Html.div [ Attr.class "ts-summary" ] [ Html.text t.summary ]
        ]
