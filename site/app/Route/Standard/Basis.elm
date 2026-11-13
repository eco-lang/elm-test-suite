module Route.Standard.Basis exposing (ActionData, Data, Model, Msg, RouteParams, route)

{-| The initial basis of A Standard Definition of Elm?, its types and values, each with a page of its own.
-}

import BackendTask exposing (BackendTask)
import Content
import FatalError exposing (FatalError)
import Head
import Head.Seo as Seo
import PagesMsg exposing (PagesMsg)
import RouteBuilder exposing (App, StatelessRoute)
import Shared
import Site
import Standard exposing (Index, ItemKind(..))
import Standard.ItemView as ItemView
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
    , intro : String
    }


type alias ActionData =
    {}


route : StatelessRoute RouteParams Data ActionData
route =
    RouteBuilder.single
        { head = head
        , data =
            BackendTask.map2
                (\idx intro ->
                    { title = ItemView.listTitle BasisEntry ++ " · " ++ idx.title
                    , description = ItemView.listTitle BasisEntry ++ " of " ++ idx.title ++ ", each with a page of its own"
                    , index = idx
                    , intro = intro
                    }
                )
                Standard.index
                (Content.load "standard/basis")
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
view app _ =
    { title = app.data.title
    , body = [ View.freeze (ItemView.listPage app.data.index BasisEntry app.data.intro) ]
    }
