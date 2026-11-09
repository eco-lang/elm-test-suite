module Route.About exposing (ActionData, Data, Model, Msg, RouteParams, route)

{-| What the site is, and why A Standard Definition of Elm? is written and titled as it is.
-}

import BackendTask
import FatalError exposing (FatalError)
import Head
import Head.Seo as Seo
import Html
import Html.Attributes as Attr
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
    Seo.summaryLarge
        { canonicalUrlOverride = Nothing
        , siteName = Site.title
        , image = Site.socialImage
        , description = "About " ++ Site.title ++ ": a test suite for Elm compilers, and A Standard Definition of Elm?"
        , locale = Nothing
        , title = "About · " ++ Site.title
        }
        |> Seo.website


view : App Data ActionData RouteParams -> Shared.Model -> View (PagesMsg Msg)
view _ _ =
    { title = "About · " ++ Site.title
    , body =
        [ Html.h1 [ Attr.class "ts-h1" ] [ Html.text "About" ]
        , Html.p [ Attr.class "ts-lede" ]
            [ Html.text (Site.title ++ " has two parts: ")
            , Route.link [] [ Html.em [] [ Html.text bookTitle ] ] Route.Standard
            , Html.text ", a precise specification of the Elm language, and the "
            , Route.link [] [ Html.text "results" ] Route.Results
            , Html.text " of a suite of Elm programs run under several compilers, many of which check the specification."
            ]
        , section "Why the title is a question"
            [ para
                [ Html.text "The working title of this specification is "
                , Html.em [] [ Html.text bookTitle ]
                , Html.text " That could be misread, so let me explain."
                ]
            , para
                [ Html.text "There is no Standard Elm. Elm is a programming language created and maintained by Evan Czaplicki, and I have no authority to say what its definition should be standardised to. That is why the working title is a question: could this be acceptable as a standard definition of Elm?" ]
            ]
        , section "Modelled on The Definition of Standard ML"
            [ para
                [ Html.text "The book follows "
                , Html.em [] [ Html.text "The Definition of Standard ML (Revised)" ]
                , Html.text ", by Robin Milner, Mads Tofte, Robert Harper and David MacQueen (MIT Press, 1997). That book is the archetype for this one, which uses the same style, techniques and structure: a grammar, inference rules for the static and dynamic semantics, derived forms, and an initial basis."
                ]
            , para
                [ Html.text "As a language, Elm is closest to Standard ML, but it leaves out much of Standard ML: exceptions, user-defined operators, references, the module language of signatures and functors, and more. It adds row polymorphism, which types extensible records. It has a cleaner syntax, and it aims to have no runtime exceptions." ]
            ]
        , section "Bug or feature?"
            [ para
                [ Html.text "I am writing a new compiler for Elm, based on the existing implementations. Elm has not yet reached version 1.0.0, so it is still considered to be in flux. Its existing implementations target JavaScript only, and inevitably inherit some quirks of that platform, despite the language's valued contribution to making applications more reliable and consistent. Sometimes I look at how Elm handles something and have to ask myself: is this a bug or a feature?" ]
            ]
        , section "What is the correct way to implement Elm?"
            [ para
                [ Html.text "I draw on three main sources for guidance: ML and the Hindley-Milner type system; IEEE 754 for floating-point arithmetic; and Unicode for text. Where Elm's behaviour is ambiguous I have leaned towards what those standards say, while giving consideration to efficient implementation and to the rule of no runtime exceptions. That rule requires every function to be total, which sometimes means giving an answer that is not the mathematically correct one: "
                , Html.code [] [ Html.text "modBy 0 x" ]
                , Html.text " is 0, for instance, where mathematics has no answer."
                ]
            , para
                [ Html.text "I am trying to find out what a correct implementation of Elm should be and how it should behave, by specifying that precisely, and by making explainable engineering decisions where a compromise has to be found to make that possible." ]
            ]
        , Html.p [ Attr.style "margin" "28px 0 8px" ]
            [ Route.link [ Attr.class "sd-button" ] [ Html.text "OK, Got It! →" ] Route.Standard ]
        ]
    }


bookTitle : String
bookTitle =
    "A Standard Definition of Elm?"


section : String -> List (Html.Html msg) -> Html.Html msg
section heading content =
    Html.section [ Attr.class "ts-section", Attr.style "max-width" "760px" ]
        (Html.h2 [ Attr.class "ts-h2" ] [ Html.text heading ] :: content)


para : List (Html.Html msg) -> Html.Html msg
para =
    Html.p [ Attr.class "sd-p" ]
