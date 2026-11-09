module Shared exposing (Data, Model, Msg(..), SharedMsg(..), template)

import BackendTask exposing (BackendTask)
import Data exposing (Report)
import Discussions
import Effect exposing (Effect)
import FatalError exposing (FatalError)
import Html exposing (Html)
import Html.Attributes as Attr
import Icons
import Pages.Flags
import Pages.PageUrl exposing (PageUrl)
import Route exposing (Route)
import SharedTemplate exposing (SharedTemplate)
import Site
import Style
import Task
import UrlPath exposing (UrlPath)
import View exposing (View)


template : SharedTemplate Msg Model Data msg
template =
    { init = init
    , update = update
    , view = view
    , data = data
    , subscriptions = subscriptions
    , onPageChange = Just (\page -> PageChanged page.path)
    }


type Msg
    = StartDiscussions
    | PageChanged UrlPath
    | DiscussionsMsg Discussions.Msg


{-| The run's report: the header and footer show where it came from.
-}
type alias Data =
    Report


type SharedMsg
    = NoOpShared


{-| The discussions of the site's categories on GitHub, fetched once per visit by the browser
(see `Discussions`).
-}
type alias Model =
    { discussions : Discussions.State }


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
init _ page =
    let
        model =
            { discussions = Discussions.init }
    in
    -- The fetch starts from a message, not here: init also runs when the pages are pre-rendered,
    -- whose HTML should not say the discussions are loading.
    case page of
        Just p ->
            if Discussions.wanted p.path.path then
                ( model, Effect.fromCmd (Task.perform (\_ -> StartDiscussions) (Task.succeed ())) )

            else
                ( model, Effect.none )

        Nothing ->
            ( model, Effect.none )


update : Msg -> Model -> ( Model, Effect Msg )
update msg model =
    case msg of
        StartDiscussions ->
            fetchDiscussions model

        PageChanged path ->
            startDiscussions path model

        DiscussionsMsg m ->
            let
                ( discussions, cmd ) =
                    Discussions.update m model.discussions
            in
            ( { model | discussions = discussions }, Effect.fromCmd (Cmd.map DiscussionsMsg cmd) )


{-| Starts fetching the discussions on the first page that shows them.
-}
startDiscussions : UrlPath -> Model -> ( Model, Effect Msg )
startDiscussions path model =
    if Discussions.wanted path then
        fetchDiscussions model

    else
        ( model, Effect.none )


{-| Fetches the discussions, unless they are fetched or being fetched already.
-}
fetchDiscussions : Model -> ( Model, Effect Msg )
fetchDiscussions model =
    let
        ( discussions, cmd ) =
            Discussions.start model.discussions
    in
    ( { model | discussions = discussions }, Effect.fromCmd (Cmd.map DiscussionsMsg cmd) )


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
                    [ Icons.elmTangram "ts-brand-mark"
                    , Html.text Site.title
                    ]
                    Route.About
                , Html.nav [ Attr.class "ts-nav" ]
                    [ Route.link [] [ Html.text "About" ] Route.About
                    , Route.link [] [ Html.text "Standard" ] Route.Standard
                    , Route.link [] [ Html.text "Results" ] Route.Results
                    ]
                , Html.a
                    [ Attr.class "ts-github"
                    , Attr.href (repoUrl report)
                    , Attr.target "_blank"
                    , Attr.rel "noopener noreferrer"
                    , Attr.title "Source on GitHub (opens in a new tab)"
                    , Attr.attribute "aria-label" "Source on GitHub (opens in a new tab)"
                    ]
                    [ Icons.github "ts-github-mark" ]
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
