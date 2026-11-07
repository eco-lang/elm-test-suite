module Discussions exposing
    ( Discussion
    , Msg
    , Problem(..)
    , State(..)
    , about
    , decoder
    , displayTitle
    , firstPageUrl
    , grouped
    , inCategory
    , init
    , keysOf
    , nextPage
    , readPage
    , start
    , update
    , wanted
    )

{-| The discussions of the site's categories, fetched by the browser from GitHub's REST API, which
needs no token for reading and allows requests from any site. One fetch (100 discussions a page)
serves every page of a visit: `Shared` keeps the result. See `plans/github-discussions.md`.
-}

import Dict exposing (Dict)
import Discuss exposing (Category)
import Http
import Json.Decode as Decode exposing (Decoder)
import Regex exposing (Regex)
import UrlPath exposing (UrlPath)


type alias Discussion =
    { number : Int
    , title : String
    , keys : List String
    , category : Category
    , author : String
    , comments : Int
    , answered : Bool
    , closed : Bool
    , updated : String
    , url : String
    }


type State
    = NotAsked
    | Loading Int (List Discussion)
    | Loaded (List Discussion)
    | Failed Problem


type Problem
    = RateLimited (Maybe Int)
    | Unavailable String


type Msg
    = GotPage Int (Result Problem Page)


type alias Page =
    { discussions : List Discussion
    , next : Maybe String
    }


init : State
init =
    NotAsked


{-| The pages that show discussions: the book, the projects and tests, and the discussion lists.
The fetch starts on the first of them that a reader opens.
-}
wanted : UrlPath -> Bool
wanted path =
    case path of
        first :: _ ->
            List.member first [ "standard", "projects", "discussions" ]

        [] ->
            False


start : State -> ( State, Cmd Msg )
start state =
    case state of
        NotAsked ->
            ( Loading 1 [], fetch 1 firstPageUrl )

        _ ->
            ( state, Cmd.none )


{-| At most this many pages (100 discussions each) are read, to bound the requests of a visit.
-}
maxPages : Int
maxPages =
    10


update : Msg -> State -> ( State, Cmd Msg )
update msg state =
    case ( msg, state ) of
        ( GotPage n (Ok page), Loading _ sofar ) ->
            let
                all =
                    sofar ++ page.discussions
            in
            case page.next of
                Just url ->
                    if n < maxPages then
                        ( Loading (n + 1) all, fetch (n + 1) url )

                    else
                        ( Loaded all, Cmd.none )

                Nothing ->
                    ( Loaded all, Cmd.none )

        ( GotPage _ (Err problem), Loading _ _ ) ->
            ( Failed problem, Cmd.none )

        _ ->
            ( state, Cmd.none )


firstPageUrl : String
firstPageUrl =
    "https://api.github.com/repos/" ++ Discuss.repo ++ "/discussions?per_page=100"


fetch : Int -> String -> Cmd Msg
fetch n url =
    Http.request
        { method = "GET"
        , headers = []
        , url = url
        , body = Http.emptyBody
        , expect = Http.expectStringResponse (GotPage n) readPage
        , timeout = Just 20000
        , tracker = Nothing
        }


{-| A reply of GitHub: a page of discussions, or what went wrong. Its rate limit for requests
without a token is reported apart, with the time it resets.
-}
readPage : Http.Response String -> Result Problem { discussions : List Discussion, next : Maybe String }
readPage response =
    case response of
        Http.GoodStatus_ meta text ->
            case Decode.decodeString (Decode.list (Decode.maybe decoder)) text of
                Ok discussions ->
                    Ok { discussions = List.filterMap identity discussions, next = nextPage (header "link" meta) }

                Err _ ->
                    Err (Unavailable "GitHub's reply could not be read")

        Http.BadStatus_ meta _ ->
            if (meta.statusCode == 403 || meta.statusCode == 429) && header "x-ratelimit-remaining" meta == Just "0" then
                Err (RateLimited (header "x-ratelimit-reset" meta |> Maybe.andThen String.toInt))

            else
                Err (Unavailable ("GitHub replied " ++ String.fromInt meta.statusCode))

        Http.Timeout_ ->
            Err (Unavailable "GitHub did not reply in time")

        Http.NetworkError_ ->
            Err (Unavailable "GitHub could not be reached")

        Http.BadUrl_ _ ->
            Err (Unavailable "bad address")


{-| A response header, whatever the case of its name.
-}
header : String -> Http.Metadata -> Maybe String
header name meta =
    meta.headers
        |> Dict.toList
        |> List.filter (\( k, _ ) -> String.toLower k == name)
        |> List.head
        |> Maybe.map Tuple.second


{-| The address of the next page, from a `Link` header such as
`<https://...&page=2>; rel="next", <https://...&page=5>; rel="last"`.
-}
nextPage : Maybe String -> Maybe String
nextPage link =
    link
        |> Maybe.map (String.split ",")
        |> Maybe.withDefault []
        |> List.filter (String.contains "rel=\"next\"")
        |> List.head
        |> Maybe.andThen
            (\part ->
                case String.split ">" part of
                    url :: _ ->
                        case String.split "<" url of
                            [ _, u ] ->
                                Just (String.trim u)

                            _ ->
                                Nothing

                    [] ->
                        Nothing
            )



-- DECODING


{-| A discussion of one of the site's categories; `Nothing` for one of another category.
-}
decoder : Decoder Discussion
decoder =
    Decode.at [ "category", "slug" ] Decode.string
        |> Decode.andThen
            (\slug ->
                case Discuss.categoryFromSlug slug of
                    Just category ->
                        discussion category

                    Nothing ->
                        Decode.fail ("another category: " ++ slug)
            )


discussion : Category -> Decoder Discussion
discussion category =
    Decode.map8
        (\number rawTitle author comments answered closed updated url ->
            { number = number
            , title = displayTitle rawTitle
            , keys = keysOf rawTitle
            , category = category
            , author = author
            , comments = comments
            , answered = answered
            , closed = closed
            , updated = updated
            , url = url
            }
        )
        (Decode.field "number" Decode.int)
        (Decode.field "title" Decode.string)
        (Decode.oneOf [ Decode.at [ "user", "login" ] Decode.string, Decode.succeed "ghost" ])
        (Decode.oneOf [ Decode.field "comments" Decode.int, Decode.succeed 0 ])
        (Decode.oneOf [ Decode.field "answer_chosen_at" (Decode.nullable Decode.string) |> Decode.map ((/=) Nothing), Decode.succeed False ])
        (Decode.oneOf [ Decode.field "state" Decode.string |> Decode.map ((==) "closed"), Decode.succeed False ])
        (Decode.field "updated_at" Decode.string)
        (Decode.field "html_url" Decode.string)



-- KEYS


keyPattern : Regex
keyPattern =
    Regex.fromString "\\[\\s*((?:r|res|df|b|ch|t|p):[^\\]\\s]+)\\s*\\]"
        |> Maybe.withDefault Regex.never


{-| The keys in a title: `[r:d-atexp-var] [t:elm-bugs/SomeTest] Why ...` has two.
-}
keysOf : String -> List String
keysOf title =
    Regex.find keyPattern title
        |> List.filterMap (.submatches >> List.head >> Maybe.andThen identity)


{-| A title without its keys.
-}
displayTitle : String -> String
displayTitle title =
    case String.trim (String.join " " (String.words (Regex.replace keyPattern (\_ -> "") title))) of
        "" ->
            "(untitled)"

        t ->
            t



-- SELECTING


{-| The discussions with a key that the test accepts, the most recently active first.
-}
about : (String -> Bool) -> List Discussion -> List Discussion
about accepts discussions =
    discussions
        |> List.filter (.keys >> List.any accepts)
        |> newestFirst


inCategory : Category -> List Discussion -> List Discussion
inCategory category =
    List.filter (\d -> d.category == category)


newestFirst : List Discussion -> List Discussion
newestFirst =
    List.sortBy .updated >> List.reverse


{-| The discussions by key, a discussion under each of its keys and one without a key under "",
the group with the most recent activity first.
-}
grouped : List Discussion -> List ( String, List Discussion )
grouped discussions =
    let
        add d dict =
            List.foldl
                (\k acc -> Dict.update k (\v -> Just (d :: Maybe.withDefault [] v)) acc)
                dict
                (if List.isEmpty d.keys then
                    [ "" ]

                 else
                    d.keys
                )

        latest ( _, ds ) =
            ds |> List.map .updated |> List.maximum |> Maybe.withDefault ""
    in
    List.foldl add Dict.empty discussions
        |> Dict.toList
        |> List.map (Tuple.mapSecond newestFirst)
        |> List.sortBy latest
        |> List.reverse
