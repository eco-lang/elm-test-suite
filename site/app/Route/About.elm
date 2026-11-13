module Route.About exposing (ActionData, Data, Model, Msg, RouteParams, route)

{-| What the site is, and why A Standard Definition of Elm? is written and titled as it is: the
Markdown of content/about.md.
-}

import BackendTask
import Content
import Dict
import FatalError exposing (FatalError)
import Head
import Head.Seo as Seo
import Html
import Html.Attributes as Attr
import PagesMsg exposing (PagesMsg)
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
    { content : String }


type alias ActionData =
    {}


route : StatelessRoute RouteParams Data ActionData
route =
    RouteBuilder.single
        { head = head
        , data = BackendTask.map (\c -> { content = c }) (Content.load "about")
        }
        |> RouteBuilder.buildNoState { view = view }


head : App Data ActionData RouteParams -> List Head.Tag
head _ =
    Seo.summaryLarge
        { canonicalUrlOverride = Nothing
        , siteName = Site.title
        , image = Site.socialImage
        , description = "About " ++ Site.title ++ ": a test suite for Elm compilers, and A Standard Definition of Elm?"
        , locale = Nothing
        , title = "About · " ++ Site.title
        }
        |> Seo.website


{-| The page is content/about.md, rendered.
-}
view : App Data ActionData RouteParams -> Shared.Model -> View (PagesMsg Msg)
view app _ =
    { title = "About · " ++ Site.title
    , body =
        [ Html.div [ Attr.class "ts-prose" ]
            (Content.view Content.Site { vars = Dict.empty, slots = Dict.empty } app.data.content)
        ]
    }
