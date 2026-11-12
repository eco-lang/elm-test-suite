module Route.Standard.Restrictions.Restriction_ exposing (ActionData, Data, Model, Msg, RouteParams, route)

{-| One restriction, at an address made from its name.
-}

import BackendTask exposing (BackendTask)
import BackendTask.File
import Data exposing (TestRef)
import Discuss
import DiscussionsView
import FatalError exposing (FatalError)
import Head
import Json.Decode as Decode
import Head.Seo as Seo
import Html exposing (Html)
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
    { restriction : String }


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
    , lean : Maybe Lean
    }


{-| The restriction's statement in the Lean mechanisation (plan step 8), when it is decided on the
syntax tree: its `Prop`, where it is, and the written programs that break it.
-}
type alias Lean =
    { prop : String, file : String, line : Int, broken : List String }


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
                >> List.filter (\it -> it.kind == Restriction)
                >> List.filterMap (\it -> Just { restriction = it.slug })
            )


data : RouteParams -> BackendTask FatalError Data
data params =
    BackendTask.map4
        (\idx it tests lean ->
            { title = Render.itemKindName it.kind ++ " " ++ it.slug ++ " · " ++ idx.title
            , description = ItemView.description idx it
            , slug = it.slug
            , index = idx
            , item = it
            , tests = tests
            , lean = lean
            }
        )
        Standard.index
        (Standard.item Restriction params.restriction)
        (Data.testsChecking Data.Restriction params.restriction)
        (leanOf params.restriction)


leanOf : String -> BackendTask FatalError (Maybe Lean)
leanOf slug =
    BackendTask.File.jsonFile
        (Decode.maybe
            (Decode.field slug
                (Decode.map4 Lean
                    (Decode.field "prop" Decode.string)
                    (Decode.field "file" Decode.string)
                    (Decode.field "line" Decode.int)
                    (Decode.field "broken" (Decode.list Decode.string))
                )
            )
        )
        "data-standard/mechanisation/restrictions.json"
        |> BackendTask.onError (\_ -> BackendTask.succeed Nothing)


leanSection : Maybe Lean -> Html msg
leanSection lean =
    case lean of
        Nothing ->
            Html.text ""

        Just l ->
            Html.section [ Attr.class "ts-section", Attr.id "lean" ]
                [ Html.h2 [ Attr.class "ts-h2" ] [ Html.text "In Lean" ]
                , Html.p [ Attr.class "ts-small" ]
                    [ Html.text "This restriction is decided on the syntax tree, as the book states it, by "
                    , Html.code [] [ Html.text l.prop ]
                    , Html.text (" (" ++ l.file ++ ", line " ++ String.fromInt l.line ++ "), whose decider the kernel runs; each written test program has a theorem that it meets the restrictions, or that it breaks this one. ")
                    , Html.text
                        (case l.broken of
                            [] ->
                                "No written test program breaks it."

                            names ->
                                "Broken by: " ++ String.join ", " names ++ "."
                        )
                    ]
                ]


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
            ItemView.itemKey Restriction slug
    in
    { title = app.data.title
    , body =
        [ View.freeze (ItemView.itemPage app.data.index app.data.item)
        , View.freeze (TestsView.section "restriction" app.data.tests)
        , View.freeze (Html.div [ Attr.class "sd-book" ] [ leanSection app.data.lean ])
        , Html.div [ Attr.class "sd-book" ]
            [ DiscussionsView.section
                { category = Discuss.Standard
                , key = key
                , noun = ItemView.itemNoun Restriction
                , url = Site.canonicalUrl ++ Render.itemHref Restriction slug
                , context = app.data.description ++ "."
                }
                ((==) key)
                shared.discussions
            ]
        , View.freeze (ItemView.itemFoot app.data.index app.data.item)
        ]
    }
