module TestList exposing (Model, Msg, init, tagLink, update, view, xfailChip)

{-| The filterable table of tests on a project's page and on a tag's page: the filter chips, the
search box and one row per test, with its outcome under each compiler.
-}

import Data exposing (Compiler, Status(..), TestRow)
import Html exposing (Html)
import Html.Attributes as Attr
import Html.Events as Events
import Route
import Ui


type Filter
    = All
    | FailingSomewhere
    | Differing
    | FailingUnder Int


type alias Model =
    { filter : Filter
    , search : String
    }


type Msg
    = SetFilter Filter
    | SetSearch String


init : Model
init =
    { filter = All, search = "" }


update : Msg -> Model -> Model
update msg model =
    case msg of
        SetFilter filter ->
            { model | filter = filter }

        SetSearch search ->
            { model | search = search }


keep : Bool -> Model -> TestRow -> Bool
keep showProject model row =
    let
        statuses =
            List.map .status row.outcomes

        matchesFilter =
            case model.filter of
                All ->
                    True

                FailingSomewhere ->
                    List.member Fail statuses

                Differing ->
                    case statuses of
                        first :: rest ->
                            List.any ((/=) first) rest

                        [] ->
                            False

                FailingUnder i ->
                    List.drop i statuses |> List.head |> (==) (Just Fail)

        needle =
            String.toLower (String.trim model.search)
    in
    matchesFilter
        && (String.isEmpty needle
                || String.contains needle (String.toLower row.name)
                || String.contains needle (String.toLower row.summary)
                || (showProject && String.contains needle (String.toLower row.project))
           )


{-| The table of `rows`. With `showProject`, each test's name is preceded by its project's (a tag's
tests come from several projects); `hideTag` is the tag of the page, not repeated on every row.
-}
view : { compilers : List Compiler, rows : List TestRow, showProject : Bool, hideTag : Maybe String } -> Model -> List (Html Msg)
view config model =
    let
        shown =
            List.filter (keep config.showProject model) config.rows

        chip filter label =
            Html.button
                [ Attr.class
                    (if model.filter == filter then
                        "ts-chip ts-chip-active"

                     else
                        "ts-chip"
                    )
                , Events.onClick (SetFilter filter)
                ]
                [ Html.text label ]
    in
    [ Html.div [ Attr.class "ts-filters" ]
        ([ chip All ("All " ++ String.fromInt (List.length config.rows))
         , chip FailingSomewhere "Failing anywhere"
         , chip Differing "Outcome differs"
         ]
            ++ List.indexedMap (\i c -> chip (FailingUnder i) ("Failing under " ++ c.name)) config.compilers
            ++ [ Html.input
                    [ Attr.class "ts-input"
                    , Attr.placeholder "Search tests"
                    , Attr.type_ "search"
                    , Attr.value model.search
                    , Events.onInput SetSearch
                    ]
                    []
               ]
        )
    , Html.p [ Attr.class "ts-muted ts-small" ]
        [ Html.text ("Showing " ++ String.fromInt (List.length shown) ++ " of " ++ String.fromInt (List.length config.rows) ++ " tests. Hover over a badge for the reason.") ]
    , Html.div [ Attr.class "ts-scroll" ]
        [ Html.table [ Attr.class "ts-table" ]
            [ Html.thead []
                [ Html.tr []
                    (Html.th [] [ Html.text "Test" ]
                        :: List.map (\c -> Html.th [ Attr.class "ts-center" ] [ Html.text c.name ]) config.compilers
                    )
                ]
            , Html.tbody [] (List.map (testRow config) shown)
            ]
        ]
    ]


testRow : { a | showProject : Bool, hideTag : Maybe String } -> TestRow -> Html msg
testRow config row =
    let
        tags =
            List.filter (\t -> Just t /= config.hideTag) row.tags
    in
    Html.tr []
        (Html.td []
            [ if config.showProject then
                Html.span [ Attr.class "ts-muted ts-small" ] [ Html.text (row.project ++ " / ") ]

              else
                Html.text ""
            , Route.link [ Attr.class "ts-test-name" ]
                [ Html.text row.name ]
                (Route.Projects__Project___Test_ { project = row.project, test = row.name })
            , if row.compileError then
                Html.span [ Attr.class "ts-muted ts-small" ] [ Html.text "  (must not compile)" ]

              else
                Html.text ""
            , xfailChip row.xfail
            , if List.isEmpty tags then
                Html.text ""

              else
                Html.span [] (List.map tagLink tags)
            , Html.div [ Attr.class "ts-summary" ] [ Html.text (truncate 220 row.summary) ]
            ]
            :: List.map
                (\o -> Html.td [ Attr.class "ts-center" ] [ Ui.statusBadgeWithReason o.status o.reason ])
                row.outcomes
        )


{-| The mark of a test that is expected to fail, with the reason as its title.
-}
xfailChip : Maybe String -> Html msg
xfailChip xfail =
    case xfail of
        Just reason ->
            Html.span [ Attr.class "ts-xfail", Attr.title ("Expected to fail: " ++ reason) ] [ Html.text "XFAIL" ]

        Nothing ->
            Html.text ""


{-| A tag, as a link to its page.
-}
tagLink : String -> Html msg
tagLink tag =
    Route.link [ Attr.class "ts-tag" ] [ Html.text tag ] (Route.Tags__Tag_ { tag = tag })


truncate : Int -> String -> String
truncate n s =
    if String.length s > n then
        String.left (n - 1) s ++ "…"

    else
        s
