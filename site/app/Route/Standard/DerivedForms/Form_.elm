module Route.Standard.DerivedForms.Form_ exposing (ActionData, Data, Model, Msg, RouteParams, route)

{-| One derived form, at an address made from its name.
-}

import BackendTask exposing (BackendTask)
import FatalError exposing (FatalError)
import Head
import Head.Seo as Seo
import Pages.Url
import PagesMsg exposing (PagesMsg)
import RouteBuilder exposing (App, StatelessRoute)
import Shared
import Site
import Standard exposing (Index, Item, ItemKind(..))
import Standard.ItemView as ItemView
import Standard.Render as Render
import View exposing (View)


type alias Model =
    {}


type alias Msg =
    ()


type alias RouteParams =
    { form : String }


{-| `index` and `item` are used only inside `View.freeze`, so elm-pages leaves them out of the data
sent to the browser; the page title and description are kept apart for that reason.
-}
type alias Data =
    { title : String
    , description : String
    , index : Index
    , item : Item
    }


type alias ActionData =
    {}


route : StatelessRoute RouteParams Data ActionData
route =
    RouteBuilder.preRender
        { head = head
        , pages = pages
        , data = data
        }
        |> RouteBuilder.buildNoState { view = view }


pages : BackendTask FatalError (List RouteParams)
pages =
    Standard.index
        |> BackendTask.map
            (.items
                >> List.filter (\it -> it.kind == DerivedForm)
                >> List.filterMap (\it -> Just { form = it.slug })
            )


data : RouteParams -> BackendTask FatalError Data
data params =
    BackendTask.map2
        (\idx it ->
            { title = Render.itemKindName it.kind ++ " " ++ it.slug ++ " · " ++ idx.title
            , description = ItemView.description idx it
            , index = idx
            , item = it
            }
        )
        Standard.index
        (Standard.item DerivedForm (params.form))


head : App Data ActionData RouteParams -> List Head.Tag
head app =
    Seo.summary
        { canonicalUrlOverride = Nothing
        , siteName = Site.title
        , image =
            { url = Pages.Url.external ""
            , alt = app.data.title
            , dimensions = Nothing
            , mimeType = Nothing
            }
        , description = app.data.description
        , locale = Nothing
        , title = app.data.title
        }
        |> Seo.website


view : App Data ActionData RouteParams -> Shared.Model -> View (PagesMsg Msg)
view app _ =
    { title = app.data.title
    , body = [ View.freeze (ItemView.itemPage app.data.index app.data.item) ]
    }
