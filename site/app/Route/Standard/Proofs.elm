module Route.Standard.Proofs exposing (ActionData, Data, Model, Msg, RouteParams, route)

{-| The Lean proofs of the mechanisation of A Standard Definition of Elm?, each with a page of its own.
-}

import BackendTask exposing (BackendTask)
import Content
import FatalError exposing (FatalError)
import Head
import Head.Seo as Seo
import Mechanisation
import Mechanisation.View as MechView
import PagesMsg exposing (PagesMsg)
import RouteBuilder exposing (App, StatelessRoute)
import Shared
import Site
import Standard exposing (Index)
import View exposing (View)


type alias Model =
    {}


type alias Msg =
    ()


type alias RouteParams =
    {}


{-| `index` and `mechanisation` are used only inside `View.freeze`, so they are not sent to the browser.
-}
type alias Data =
    { title : String
    , description : String
    , index : Index
    , mechanisation : Mechanisation.Index
    , intro : String
    }


type alias ActionData =
    {}


route : StatelessRoute RouteParams Data ActionData
route =
    RouteBuilder.single
        { head = head
        , data =
            BackendTask.map3
                (\idx mech intro ->
                    { title = "Lean proofs · " ++ idx.title
                    , description = "The Lean 4 proofs of the mechanisation of " ++ idx.title ++ ", each with a page of its own"
                    , index = idx
                    , mechanisation = mech
                    , intro = intro
                    }
                )
                Standard.index
                Mechanisation.index
                (Content.load "standard/proofs")
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
    , body = [ View.freeze (MechView.listPage app.data.index app.data.mechanisation app.data.intro) ]
    }
