module DiscussionsView exposing (keyHref, overview, section)

{-| The views of the discussions: the Discussions section of a page, and the list of all the
discussions of a category. They are rendered outside `View.freeze`, from `Shared`'s state, so the
list fills in once the browser has fetched it; the links to GitHub are plain links and work without
JavaScript.
-}

import Discuss exposing (Category, Target)
import Discussions exposing (Discussion, Problem(..), State(..))
import Html exposing (Html)
import Html.Attributes as Attr
import Route
import Standard exposing (ItemKind(..))
import Standard.Render as Render
import Time


external : String -> List (Html msg) -> Html msg
external url =
    Html.a [ Attr.href url, Attr.target "_blank", Attr.rel "noopener noreferrer" ]


{-| The Discussions section of a page: the discussions whose keys `accepts` takes (usually the
page's key alone; for a project, its tests' keys too), and the links to start one and to search.
-}
section : Target -> (String -> Bool) -> State -> Html msg
section target accepts state =
    Html.section [ Attr.class "ts-section dz-section", Attr.id "discussions" ]
        [ Html.h2 [ Attr.class "dz-head" ] [ Html.text "Discussions" ]
        , case state of
            NotAsked ->
                Html.text ""

            Loading _ _ ->
                Html.p [ Attr.class "dz-status" ] [ Html.text "Loading the discussions from GitHub…" ]

            Loaded all ->
                case Discussions.about accepts (Discussions.inCategory target.category all) of
                    [] ->
                        Html.p [ Attr.class "dz-status" ] [ Html.text ("No discussions of this " ++ target.noun ++ " yet.") ]

                    found ->
                        Html.ul [ Attr.class "dz-list" ] (List.map (entry (\k -> k /= target.key)) found)

            Failed problem ->
                failure problem
        , Html.p [ Attr.class "dz-actions" ]
            [ external (Discuss.newDiscussionUrl target) [ Html.text ("Discuss this " ++ target.noun) ]
            , Html.span [ Attr.class "dz-sep" ] [ Html.text "·" ]
            , external (Discuss.searchUrl target.key) [ Html.text "Search the discussions on GitHub" ]
            ]
        , Html.p [ Attr.class "dz-note" ]
            [ Html.text "Discussions are on GitHub; one about this "
            , Html.text target.noun
            , Html.text " has "
            , Html.code [] [ Html.text ("[" ++ target.key ++ "]") ]
            , Html.text " in its title."
            ]
        ]


failure : Problem -> Html msg
failure problem =
    Html.p [ Attr.class "dz-status dz-failed" ]
        [ case problem of
            RateLimited reset ->
                Html.text
                    ("GitHub's limit on requests from your address has been reached, so the discussions cannot be shown"
                        ++ (case reset of
                                Just seconds ->
                                    " until " ++ clock seconds ++ " UTC."

                                Nothing ->
                                    " for now."
                           )
                    )

            Unavailable why ->
                Html.text ("The discussions could not be loaded (" ++ why ++ ").")
        ]


{-| Seconds since 1970 as a time of day, "14:05".
-}
clock : Int -> String
clock seconds =
    let
        t =
            Time.millisToPosix (seconds * 1000)

        two n =
            String.padLeft 2 '0' (String.fromInt n)
    in
    two (Time.toHour Time.utc t) ++ ":" ++ two (Time.toMinute Time.utc t)


{-| One discussion: its title, linking to it on GitHub, and a line about it. Keys that `show`
accepts are listed, linking to their pages.
-}
entry : (String -> Bool) -> Discussion -> Html msg
entry show d =
    Html.li [ Attr.class "dz-entry" ]
        [ external d.url [ Html.text d.title ]
        , Html.div [ Attr.class "dz-meta" ]
            (List.intersperse (Html.text " · ")
                (List.concat
                    [ [ Html.text ("#" ++ String.fromInt d.number) ]
                    , [ Html.text d.author ]
                    , [ Html.text
                            (String.fromInt d.comments
                                ++ (if d.comments == 1 then
                                        " reply"

                                    else
                                        " replies"
                                   )
                            )
                      ]
                    , if d.answered then
                        [ Html.span [ Attr.class "dz-answered" ] [ Html.text "answered" ] ]

                      else
                        []
                    , if d.closed then
                        [ Html.text "closed" ]

                      else
                        []
                    , [ Html.text ("active " ++ String.left 10 d.updated) ]
                    , List.filter show d.keys |> List.map keyLink
                    ]
                )
            )
        ]


keyLink : String -> Html msg
keyLink key =
    case keyHref key of
        Just href ->
            Html.a [ Attr.href href, Attr.class "dz-key" ] [ Html.text key ]

        Nothing ->
            Html.code [ Attr.class "dz-key" ] [ Html.text key ]


{-| The page of the site that a key is about.
-}
keyHref : String -> Maybe String
keyHref key =
    case String.split ":" key of
        [ prefix, name ] ->
            case prefix of
                "r" ->
                    Just (Render.ruleHref name)

                "res" ->
                    Just (Render.itemHref Restriction name)

                "df" ->
                    Just (Render.itemHref DerivedForm name)

                "b" ->
                    Just (Render.itemHref BasisEntry name)

                "ch" ->
                    Just (Render.chapterHref name "")

                "p" ->
                    Just (Route.toString (Route.Projects__Project_ { project = name }))

                "t" ->
                    case String.split "/" name of
                        [ project, test ] ->
                            Just (Route.toString (Route.Projects__Project___Test_ { project = project, test = test }))

                        _ ->
                            Nothing

                _ ->
                    Nothing

        _ ->
            Nothing


{-| Every discussion of a category, by the item it is about, the most recently active first.
-}
overview : Category -> State -> Html msg
overview category state =
    case state of
        NotAsked ->
            Html.p [ Attr.class "dz-status" ]
                [ external (Discuss.categoryUrl category) [ Html.text "See the discussions on GitHub" ]
                , Html.text "."
                ]

        Loading _ _ ->
            Html.p [ Attr.class "dz-status" ] [ Html.text "Loading the discussions from GitHub…" ]

        Failed problem ->
            failure problem

        Loaded all ->
            case Discussions.grouped (Discussions.inCategory category all) of
                [] ->
                    Html.p [ Attr.class "dz-status" ] [ Html.text "No discussions yet." ]

                groups ->
                    Html.div []
                        (List.map
                            (\( key, ds ) ->
                                Html.section [ Attr.class "dz-group" ]
                                    [ Html.h3 [ Attr.class "dz-group-head" ]
                                        [ if String.isEmpty key then
                                            Html.text "General"

                                          else
                                            keyLink key
                                        , Html.span [ Attr.class "dz-count" ] [ Html.text (String.fromInt (List.length ds)) ]
                                        ]
                                    , Html.ul [ Attr.class "dz-list" ] (List.map (entry (\k -> k /= key)) ds)
                                    ]
                            )
                            groups
                        )
