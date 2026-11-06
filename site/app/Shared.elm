module Shared exposing (Data, Model, Msg(..), SharedMsg(..), template)

import BackendTask exposing (BackendTask)
import Data exposing (Report)
import Effect exposing (Effect)
import FatalError exposing (FatalError)
import Html exposing (Html)
import Html.Attributes as Attr
import Pages.Flags
import Pages.PageUrl exposing (PageUrl)
import Route exposing (Route)
import SharedTemplate exposing (SharedTemplate)
import Style
import UrlPath exposing (UrlPath)
import View exposing (View)


template : SharedTemplate Msg Model Data msg
template =
    { init = init
    , update = update
    , view = view
    , data = data
    , subscriptions = subscriptions
    , onPageChange = Nothing
    }


type Msg
    = NoOp


{-| The run's report: the header and footer show where it came from.
-}
type alias Data =
    Report


type SharedMsg
    = NoOpShared


type alias Model =
    {}


init :
    Pages.Flags.Flags
    ->
        Maybe
            { path :
                { path : UrlPath
                , query : Maybe String
                , fragment : Maybe String
                }
            , metadata : route
            , pageUrl : Maybe PageUrl
            }
    -> ( Model, Effect Msg )
init _ _ =
    ( {}, Effect.none )


update : Msg -> Model -> ( Model, Effect Msg )
update _ model =
    ( model, Effect.none )


subscriptions : UrlPath -> Model -> Sub Msg
subscriptions _ _ =
    Sub.none


data : BackendTask FatalError Data
data =
    Data.report


view :
    Data
    ->
        { path : UrlPath
        , route : Maybe Route
        }
    -> Model
    -> (Msg -> msg)
    -> View msg
    -> { body : List (Html msg), title : String }
view report _ _ _ pageView =
    { body =
        [ Style.styleNode
        , Html.header [ Attr.class "ts-header" ]
            [ Html.div [ Attr.class "ts-header-inner" ]
                [ Route.link [ Attr.class "ts-brand" ]
                    [ Html.span [ Attr.class "ts-brand-mark" ] []
                    , Html.text "Elm test suite"
                    ]
                    Route.Index
                , Html.nav [ Attr.class "ts-nav" ]
                    [ Route.link [] [ Html.text "Results" ] Route.Index
                    , Html.a [ Attr.href (Route.toString Route.Index ++ "#differing") ] [ Html.text "Differences" ]
                    , externalLink (repoUrl report) "Source"
                    ]
                ]
            ]
        , Html.main_ [ Attr.class "ts-main" ] pageView.body
        , footer report
        ]
    , title = pageView.title
    }


repoUrl : Report -> String
repoUrl report =
    "https://github.com/"
        ++ (if String.isEmpty report.repository then
                "eco-lang/elm-test-suite"

            else
                report.repository
           )


externalLink : String -> String -> Html msg
externalLink href label =
    Html.a [ Attr.href href, Attr.rel "noopener" ] [ Html.text label ]


footer : Report -> Html msg
footer report =
    Html.footer [ Attr.class "ts-footer" ]
        [ Html.div [ Attr.class "ts-footer-inner" ]
            (List.filterMap identity
                [ Just (Html.span [] [ Html.text ("Generated " ++ String.replace "T" " " (String.left 16 report.generated) ++ " UTC") ])
                , Just (Html.span [] [ Html.text ("Node " ++ report.node) ])
                , if String.isEmpty report.commit then
                    Nothing

                  else
                    Just
                        (Html.span []
                            [ Html.text "Commit "
                            , externalLink (repoUrl report ++ "/commit/" ++ report.commit) (String.left 7 report.commit)
                            ]
                        )
                , if String.isEmpty report.runUrl then
                    Nothing

                  else
                    Just (externalLink report.runUrl "CI run")
                ]
            )
        ]
