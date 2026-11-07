module Route.Standard.Restrictions exposing (ActionData, Data, Model, Msg, RouteParams, route)

{-| The restrictions of The Definition of Standard Elm, each with a page of its own.
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
                        { title = ItemView.listTitle Restriction ++ " · " ++ idx.title
                        , description = ItemView.listTitle Restriction ++ " of " ++ idx.title ++ ", each with a page of its own"
                        , index = idx
                        }
                    )
        }
        |> RouteBuilder.buildNoState { view = view }


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
    , body = [ View.freeze (ItemView.listPage app.data.index Restriction) ]
    }
