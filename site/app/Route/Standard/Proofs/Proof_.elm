module Route.Standard.Proofs.Proof_ exposing (ActionData, Data, Model, Msg, RouteParams, route)

{-| One Lean theorem of the mechanisation, at an address made from its name; or, at
`/standard/proofs/kc`, the theorems generated at compile time.
-}

import BackendTask exposing (BackendTask)
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
    { proof : String }


{-| `index` and `page` are used only inside `View.freeze`, so they are not sent to the browser.
-}
type alias Data =
    { title : String
    , description : String
    , index : Index
    , page : Page
    }


type Page
    = TheoremPage Mechanisation.Proof
    | GeneratedPage Mechanisation.Generated


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
    Mechanisation.index
        |> BackendTask.map
            (\mech ->
                { proof = Mechanisation.generatedSlug } :: List.map (\t -> { proof = t.slug }) mech.theorems
            )


data : RouteParams -> BackendTask FatalError Data
data params =
    if params.proof == Mechanisation.generatedSlug then
        BackendTask.map2
            (\idx g ->
                { title = "Generated Lean theorems · " ++ idx.title
                , description = String.fromInt g.count ++ " Lean theorems, generated at compile time, that the rules of " ++ idx.title ++ " derive the expected values of test programs"
                , index = idx
                , page = GeneratedPage g
                }
            )
            Standard.index
            Mechanisation.generated

    else
        BackendTask.map2
            (\idx p ->
                { title = "Theorem " ++ p.summary.name ++ " · " ++ idx.title
                , description = description idx p
                , index = idx
                , page = TheoremPage p
                }
            )
            Standard.index
            (Mechanisation.proof params.proof)


description : Index -> Mechanisation.Proof -> String
description idx p =
    "Lean theorem "
        ++ p.summary.name
        ++ " of the mechanisation of "
        ++ idx.title
        ++ (if String.isEmpty p.summary.summary then
                ""

            else
                ": " ++ p.summary.summary
           )


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
    , body =
        [ View.freeze
            (case app.data.page of
                TheoremPage p ->
                    MechView.proofPage app.data.index p

                GeneratedPage g ->
                    MechView.generatedPage app.data.index g
            )
        ]
    }
