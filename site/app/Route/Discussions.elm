module Route.Discussions exposing (ActionData, Data, Model, Msg, RouteParams, route)

{-| Every discussion of the tests, by the test or project it is about. The list is fetched by the
browser from GitHub (see `Discussions`).
-}

import BackendTask
import Content
import Dict
import Discuss
import DiscussionsView
import FatalError exposing (FatalError)
import Head
import Head.Seo as Seo
import Html
import Html.Attributes as Attr
import PagesMsg exposing (PagesMsg)
import Route
import RouteBuilder exposing (App, StatelessRoute)
import Shared
import Site
import View exposing (View)


type alias Model =
    {}


type alias Msg =
    ()


type alias RouteParams =
    {}


type alias Data =
    { intro : String }


type alias ActionData =
    {}


route : StatelessRoute RouteParams Data ActionData
route =
    RouteBuilder.single
        { head = head
        , data = BackendTask.map (\i -> { intro = i }) (Content.load "discussions")
        }
        |> RouteBuilder.buildNoState { view = view }


head : App Data ActionData RouteParams -> List Head.Tag
head _ =
    Seo.summaryLarge
        { canonicalUrlOverride = Nothing
        , siteName = Site.title
        , image = Site.socialImage
        , description = "The discussions of the tests of " ++ Site.title ++ ", by the test or project they are about"
        , locale = Nothing
        , title = "Discussions · " ++ Site.title
        }
        |> Seo.website


view : App Data ActionData RouteParams -> Shared.Model -> View (PagesMsg Msg)
view app shared =
    { title = "Discussions · " ++ Site.title
    , body =
        [ Html.div [ Attr.class "ts-crumbs" ] [ Route.link [] [ Html.text "Results" ] Route.Results, Html.text " / " ]
        , Html.div []
            (Content.view Content.Site
                { vars = Dict.fromList [ ( "categoryUrl", Discuss.categoryUrl Discuss.Tests ) ], slots = Dict.empty }
                app.data.intro
            )
        , DiscussionsView.overview Discuss.Tests shared.discussions
        ]
    }
