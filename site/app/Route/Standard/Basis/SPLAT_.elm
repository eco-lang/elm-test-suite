module Route.Standard.Basis.SPLAT_ exposing (ActionData, Data, Model, Msg, RouteParams, route)

{-| One entry of the initial basis, at its qualified name with the dots as slashes:
`/standard/basis/Platform/Cmd/none`.
-}

import BackendTask exposing (BackendTask)
import Data exposing (TestRef)
import Discuss
import DiscussionsView
import FatalError exposing (FatalError)
import Head
import Head.Seo as Seo
import Html
import Html.Attributes as Attr
import PagesMsg exposing (PagesMsg)
import RouteBuilder exposing (App, StatelessRoute)
import Shared
import Site
import Standard exposing (Index, Item, ItemKind(..))
import Standard.ItemView as ItemView
import Standard.Render as Render
import Standard.TestsView as TestsView
import View exposing (View)


type alias Model =
    {}


type alias Msg =
    ()


type alias RouteParams =
    { splat : ( String, List String ) }


{-| `index`, `item` and `tests` are used only inside `View.freeze`, so elm-pages leaves them out of the data
sent to the browser; the page title and description are kept apart for that reason. `slug` is the item's
name as the book writes it, for the key of its discussions: the address in the browser may not
keep its case (Netlify serves a mixed-case path at its lower-case form).
-}
type alias Data =
    { title : String
    , description : String
    , slug : String
    , index : Index
    , item : Item
    , tests : List TestRef
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
                >> List.filter (\it -> it.kind == BasisEntry)
                >> List.filterMap (\it -> case String.split "." it.slug of
                            first :: rest ->
                                Just { splat = ( first, rest ) }

                            [] ->
                                Nothing)
            )


data : RouteParams -> BackendTask FatalError Data
data params =
    BackendTask.map3
        (\idx it tests ->
            { title = Render.itemKindName it.kind ++ " " ++ it.slug ++ " · " ++ idx.title
            , description = ItemView.description idx it
            , slug = it.slug
            , index = idx
            , item = it
            , tests = tests
            }
        )
        Standard.index
        (Standard.item BasisEntry (String.join "." (Tuple.first params.splat :: Tuple.second params.splat)))
        (Data.testsChecking Data.Basis (String.join "." (Tuple.first params.splat :: Tuple.second params.splat)))


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
    let
        slug =
            app.data.slug

        key =
            ItemView.itemKey BasisEntry slug
    in
    { title = app.data.title
    , body =
        [ View.freeze (ItemView.itemPage app.data.index app.data.item)
        , View.freeze (TestsView.section "entry of the basis" app.data.tests)
        , Html.div [ Attr.class "sd-book" ]
            [ DiscussionsView.section
                { category = Discuss.Standard
                , key = key
                , noun = ItemView.itemNoun BasisEntry
                , url = Site.canonicalUrl ++ Render.itemHref BasisEntry slug
                , context = app.data.description ++ "."
                }
                ((==) key)
                shared.discussions
            ]
        , View.freeze (ItemView.itemFoot app.data.index app.data.item)
        ]
    }
