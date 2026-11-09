module Route.Index exposing (ActionData, Data, Model, Msg, RouteParams, route)

{-| The root of the site, which sends the reader on to the About page, the site's main page. On
Netlify `public/_redirects` redirects `/` before this page is served; elsewhere its
`<meta http-equiv="refresh">` does, and its link does without either.
-}

import BackendTask
import FatalError exposing (FatalError)
import Head
import Html
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
    [ Head.metaRedirect (Head.raw ("0; url=" ++ Route.toString Route.About)) ]


view : App Data ActionData RouteParams -> Shared.Model -> View (PagesMsg Msg)
view _ _ =
    { title = Site.title
    , body =
        [ Html.p []
            [ Html.text "Continue to "
            , Route.link [] [ Html.text "About" ] Route.About
            , Html.text "."
            ]
        ]
    }
