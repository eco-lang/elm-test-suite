module Route.Discussions exposing (ActionData, Data, Model, Msg, RouteParams, route)

{-| Every discussion of the tests, by the test or project it is about. The list is fetched by the
browser from GitHub (see `Discussions`).
-}

import BackendTask
import Discuss
import DiscussionsView
import FatalError exposing (FatalError)
import Head
import Head.Seo as Seo
import Html
import Html.Attributes as Attr
import Pages.Url
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
    {}


type alias ActionData =
    {}


route : StatelessRoute RouteParams Data ActionData
route =
    RouteBuilder.single
        { head = head
        , data = BackendTask.succeed {}
        }
        |> RouteBuilder.buildNoState { view = view }


head : App Data ActionData RouteParams -> List Head.Tag
head _ =
    Seo.summary
        { canonicalUrlOverride = Nothing
        , siteName = Site.title
        , image =
            { url = Pages.Url.external ""
            , alt = Site.title
            , dimensions = Nothing
            , mimeType = Nothing
            }
        , description = "The discussions of the tests of " ++ Site.title ++ ", by the test or project they are about"
        , locale = Nothing
        , title = "Discussions · " ++ Site.title
        }
        |> Seo.website


view : App Data ActionData RouteParams -> Shared.Model -> View (PagesMsg Msg)
view _ shared =
    { title = "Discussions · " ++ Site.title
    , body =
        [ Html.div [ Attr.class "ts-crumbs" ] [ Route.link [] [ Html.text "Results" ] Route.Index, Html.text " / " ]
        , Html.h1 [ Attr.class "ts-h1" ] [ Html.text "Discussions" ]
        , Html.p [ Attr.class "ts-lede" ]
            [ Html.text "The tests and their results are discussed in the "
            , Html.a [ Attr.href (Discuss.categoryUrl Discuss.Tests), Attr.target "_blank", Attr.rel "noopener noreferrer" ]
                [ Html.text "Tests category of the repository's GitHub Discussions" ]
            , Html.text ". A discussion is about a test when its title holds the test's key in brackets, "
            , Html.code [] [ Html.text "[t:elm-bugs/CompilerIssue2281LongLineListTest]" ]
            , Html.text ", or about a whole project with "
            , Html.code [] [ Html.text "[p:elm-bugs]" ]
            , Html.text "; the Discuss link on each test's page starts one with the key in place, and the discussion is then shown on that page."
            ]
        , DiscussionsView.overview Discuss.Tests shared.discussions
        ]
    }
