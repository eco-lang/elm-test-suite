module Route.Standard.Discussions exposing (ActionData, Data, Model, Msg, RouteParams, route)

{-| Every discussion of A Standard Definition of Elm?, by the rule or item it is about. The list
is fetched by the browser from GitHub (see `Discussions`); the rest of the page is frozen.
-}

import BackendTask
import Discuss
import DiscussionsView
import FatalError exposing (FatalError)
import Head
import Head.Seo as Seo
import Html exposing (Html)
import Html.Attributes as Attr
import PagesMsg exposing (PagesMsg)
import Route
import RouteBuilder exposing (App, StatelessRoute)
import Shared
import Site
import Standard exposing (Index)
import Standard.Render as Render
import View exposing (View)


type alias Model =
    {}


type alias Msg =
    ()


type alias RouteParams =
    {}


{-| `index` is used only inside `View.freeze`, so it is not sent to the browser.
-}
type alias Data =
    { title : String
    , description : String
    , index : Index
    }


type alias ActionData =
    {}


route : StatelessRoute RouteParams Data ActionData
route =
    RouteBuilder.single
        { head = head
        , data =
            Standard.index
                |> BackendTask.map
                    (\idx ->
                        { title = "Discussions · " ++ idx.title
                        , description = "The discussions of " ++ idx.title ++ ", by the rule or item they are about"
                        , index = idx
                        }
                    )
        }
        |> RouteBuilder.buildNoState { view = view }


head : App Data ActionData RouteParams -> List Head.Tag
head app =
    Seo.summaryLarge
        { canonicalUrlOverride = Nothing
        , siteName = Site.title
        , image = Site.socialImage
        , description = app.data.description
        , locale = Nothing
        , title = app.data.title
        }
        |> Seo.website


view : App Data ActionData RouteParams -> Shared.Model -> View (PagesMsg Msg)
view app shared =
    { title = app.data.title
    , body =
        [ View.freeze (top app.data.index)
        , Html.div [ Attr.class "sd-book" ] [ DiscussionsView.overview Discuss.Standard shared.discussions ]
        , View.freeze (Html.div [ Attr.class "sd-book" ] [ Render.licence app.data.index ])
        ]
    }


top : Index -> Html msg
top idx =
    Html.div [ Attr.class "sd-book" ]
        [ Html.div [ Attr.class "ts-crumbs" ]
            [ Html.a [ Attr.href (Route.toString Route.Standard) ] [ Html.text idx.title ]
            , Html.span [ Attr.class "sd-edition-chip" ] [ Html.text idx.edition ]
            , Html.text " / Discussions"
            ]
        , Html.h1 [ Attr.class "sd-chapter-title" ] [ Html.text "Discussions" ]
        , Html.p [ Attr.class "sd-lede" ]
            [ Html.text "The Definition is discussed in the "
            , Html.a [ Attr.href (Discuss.categoryUrl Discuss.Standard), Attr.target "_blank", Attr.rel "noopener noreferrer" ]
                [ Html.text "Standard category of the repository's GitHub Discussions" ]
            , Html.text ". A discussion is about a rule, restriction, derived form, entry of the basis or chapter when its title holds that item's key in brackets, "
            , Html.code [] [ Html.text "[r:d-atexp-var]" ]
            , Html.text "; the Discuss link on each item's page starts one with the key in place, and the discussion is then shown on that page."
            ]
        ]
