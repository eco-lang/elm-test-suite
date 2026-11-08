module DiscussionsTest exposing (suite)

import Dict
import Discuss
import Discussions exposing (Discussion, Problem(..))
import Expect
import Http
import Json.Decode as Decode
import Test exposing (Test, describe, test)
import Url


suite : Test
suite =
    describe "Discussions"
        [ keys
        , titles
        , urls
        , paging
        , decoding
        , replies
        , selecting
        ]


keys : Test
keys =
    describe "keysOf"
        [ test "one key" <|
            \_ -> Discussions.keysOf "[r:d-atexp-var] Why a variable?" |> Expect.equal [ "r:d-atexp-var" ]
        , test "several keys, anywhere in the title" <|
            \_ ->
                Discussions.keysOf "[r:d-atexp-var] and [t:elm-bugs/SomeTest] disagree"
                    |> Expect.equal [ "r:d-atexp-var", "t:elm-bugs/SomeTest" ]
        , test "keys with dots and slashes" <|
            \_ ->
                Discussions.keysOf "[b:Platform.Cmd.none] [t:elm-bugs/CompilerIssue2281LongLineListTest]"
                    |> Expect.equal [ "b:Platform.Cmd.none", "t:elm-bugs/CompilerIssue2281LongLineListTest" ]
        , test "every prefix" <|
            \_ ->
                Discussions.keysOf "[r:a] [res:b] [df:c] [b:D.e] [ch:f] [t:g/H] [p:i]"
                    |> Expect.equal [ "r:a", "res:b", "df:c", "b:D.e", "ch:f", "t:g/H", "p:i" ]
        , test "space inside the brackets" <|
            \_ -> Discussions.keysOf "[ r:d-atexp-var ] x" |> Expect.equal [ "r:d-atexp-var" ]
        , test "an unknown prefix is not a key" <|
            \_ -> Discussions.keysOf "[x:something] [WIP] title" |> Expect.equal []
        , test "no key" <|
            \_ -> Discussions.keysOf "Welcome to elm-test-suite Discussions!" |> Expect.equal []
        ]


titles : Test
titles =
    describe "displayTitle"
        [ test "drops the keys" <|
            \_ -> Discussions.displayTitle "[r:d-atexp-var]  Why a  variable?" |> Expect.equal "Why a variable?"
        , test "keeps other brackets" <|
            \_ -> Discussions.displayTitle "[WIP] [ch:effects] Ports" |> Expect.equal "[WIP] Ports"
        , test "a title of keys alone" <|
            \_ -> Discussions.displayTitle "[r:d-atexp-var] " |> Expect.equal "(untitled)"
        ]


target : Discuss.Target
target =
    { category = Discuss.Standard
    , key = "r:d-atexp-var"
    , noun = "rule"
    , url = "https://elm-test-suite.netlify.app/standard/rules/d-atexp-var"
    , context = "Rule 66, d-atexp-var, of A Standard Definition of Elm? (Draft version 0.3)."
    }


{-| The value of a query parameter of a URL, decoded.
-}
param : String -> String -> Maybe String
param name url =
    case String.split "?" url of
        [ _, query ] ->
            query
                |> String.split "&"
                |> List.filterMap
                    (\kv ->
                        case String.split "=" kv of
                            [ k, v ] ->
                                if k == name then
                                    Url.percentDecode v

                                else
                                    Nothing

                            _ ->
                                Nothing
                    )
                |> List.head

        _ ->
            Nothing


urls : Test
urls =
    describe "Discuss"
        [ test "a new discussion is in the item's category" <|
            \_ -> param "category" (Discuss.newDiscussionUrl target) |> Expect.equal (Just "standard")
        , test "a new discussion's title starts with the key" <|
            \_ -> param "title" (Discuss.newDiscussionUrl target) |> Expect.equal (Just "[r:d-atexp-var] ")
        , test "a new discussion's body links back to the item and gives its context" <|
            \_ ->
                param "body" (Discuss.newDiscussionUrl target)
                    |> Maybe.map (\b -> String.contains target.url b && String.contains target.context b)
                    |> Expect.equal (Just True)
        , test "a test's discussion is in the Tests category" <|
            \_ ->
                param "category" (Discuss.newDiscussionUrl { target | category = Discuss.Tests, key = "t:elm-bugs/X" })
                    |> Expect.equal (Just "tests")
        , test "the address is the repository's" <|
            \_ ->
                Discuss.newDiscussionUrl target
                    |> String.startsWith "https://github.com/eco-lang/elm-test-suite/discussions/new?"
                    |> Expect.equal True
        , test "the search looks for the quoted key" <|
            \_ ->
                param "discussions_q" (Discuss.searchUrl "b:Platform.Cmd.none")
                    |> Expect.equal (Just "\"b:Platform.Cmd.none\"")
        , test "a category's page" <|
            \_ ->
                Discuss.categoryUrl Discuss.Tests
                    |> Expect.equal "https://github.com/eco-lang/elm-test-suite/discussions/categories/tests"
        ]


paging : Test
paging =
    describe "nextPage"
        [ test "the next page of a Link header" <|
            \_ ->
                Discussions.nextPage (Just "<https://api.github.com/repositories/1/discussions?per_page=100&page=2>; rel=\"next\", <https://api.github.com/repositories/1/discussions?per_page=100&page=4>; rel=\"last\"")
                    |> Expect.equal (Just "https://api.github.com/repositories/1/discussions?per_page=100&page=2")
        , test "the last page has none" <|
            \_ ->
                Discussions.nextPage (Just "<https://api.github.com/repositories/1/discussions?per_page=100&page=1>; rel=\"prev\", <https://api.github.com/repositories/1/discussions?per_page=100&page=1>; rel=\"first\"")
                    |> Expect.equal Nothing
        , test "no Link header" <|
            \_ -> Discussions.nextPage Nothing |> Expect.equal Nothing
        , test "the pages that fetch" <|
            \_ ->
                List.map Discussions.wanted [ [ "standard", "rules", "x" ], [ "projects", "elm" ], [ "discussions" ], [], [ "downloads" ] ]
                    |> Expect.equal [ True, True, True, False, False ]
        ]


decoded : List (Maybe Discussion)
decoded =
    Decode.decodeString (Decode.list (Decode.maybe Discussions.decoder)) fixture
        |> Result.withDefault []


decoding : Test
decoding =
    describe "decoder"
        [ test "every discussion of the reply is read, those of other categories as Nothing" <|
            \_ -> List.map ((/=) Nothing) decoded |> Expect.equal [ False, True, True, True ]
        , test "a discussion of the Standard category" <|
            \_ ->
                case decoded of
                    [ _, Just d, _, _ ] ->
                        Expect.equal
                            ( ( d.number, d.title, d.keys ), ( d.category, d.author, d.comments ), ( d.answered, d.closed, d.url ) )
                            ( ( 3, "Is the closure of a let polymorphic?", [ "r:d-atexp-var", "res:core-no-shadowing" ] )
                            , ( Discuss.Standard, "someone", 2 )
                            , ( True, False, "https://github.com/eco-lang/elm-test-suite/discussions/3" )
                            )

                    _ ->
                        Expect.fail "not decoded"
        , test "a closed discussion of the Tests category, its author's account deleted" <|
            \_ ->
                case decoded of
                    [ _, _, Just d, _ ] ->
                        Expect.equal ( d.category, d.closed, d.author ) ( Discuss.Tests, True, "ghost" )

                    _ ->
                        Expect.fail "not decoded"
        ]


selecting : Test
selecting =
    let
        all =
            List.filterMap identity decoded
    in
    describe "selecting"
        [ test "about a key" <|
            \_ -> Discussions.about ((==) "res:core-no-shadowing") all |> List.map .number |> Expect.equal [ 3 ]
        , test "about a project or its tests" <|
            \_ ->
                Discussions.about (\k -> k == "p:elm-bugs" || String.startsWith "t:elm-bugs/" k) all
                    |> List.map .number
                    |> Expect.equal [ 5 ]
        , test "the most recently active first" <|
            \_ -> Discussions.about (\_ -> True) all |> List.map .number |> Expect.equal [ 5, 3 ]
        , test "grouped by key, a discussion under each of its keys" <|
            \_ ->
                Discussions.grouped (Discussions.inCategory Discuss.Standard all)
                    |> List.map (\( k, ds ) -> ( k, List.map .number ds ))
                    |> List.sortBy Tuple.first
                    |> Expect.equal [ ( "r:d-atexp-var", [ 3 ] ), ( "res:core-no-shadowing", [ 3 ] ) ]
        , test "one without a key is under \"\"" <|
            \_ ->
                Discussions.grouped (Discussions.inCategory Discuss.Tests all)
                    |> List.map Tuple.first
                    |> Expect.equal [ "t:elm-bugs/BytesIssue15BytesEqualityTest", "" ]
        ]


{-| A reply of `GET /repos/eco-lang/elm-test-suite/discussions`, cut down to the fields the site
reads: the welcome post as GitHub wrote it (category Announcements) and three made up.
-}
fixture : String
fixture =
    """
[
  { "number": 2, "title": "Welcome to elm-test-suite Discussions!",
    "category": { "name": "Announcements", "slug": "announcements" },
    "user": { "login": "the-sett" }, "comments": 0, "answer_chosen_at": null, "state": "open",
    "updated_at": "2026-11-07T22:24:05Z", "html_url": "https://github.com/eco-lang/elm-test-suite/discussions/2" },
  { "number": 3, "title": "[r:d-atexp-var] [res:core-no-shadowing] Is the closure of a let polymorphic?",
    "category": { "name": "Standard", "slug": "standard" },
    "user": { "login": "someone" }, "comments": 2, "answer_chosen_at": "2026-11-08T10:00:00Z", "state": "open",
    "updated_at": "2026-11-08T10:00:00Z", "html_url": "https://github.com/eco-lang/elm-test-suite/discussions/3" },
  { "number": 4, "title": "Flaky on lamdera?",
    "category": { "name": "Tests", "slug": "tests" },
    "user": null, "comments": 1, "answer_chosen_at": null, "state": "closed",
    "updated_at": "2026-11-08T11:00:00Z", "html_url": "https://github.com/eco-lang/elm-test-suite/discussions/4" },
  { "number": 5, "title": "[t:elm-bugs/BytesIssue15BytesEqualityTest] Why does this fail everywhere?",
    "category": { "name": "Tests", "slug": "tests" },
    "user": { "login": "someone" }, "comments": 0, "answer_chosen_at": null, "state": "open",
    "updated_at": "2026-11-08T12:00:00Z", "html_url": "https://github.com/eco-lang/elm-test-suite/discussions/5" }
]
"""


meta : Int -> List ( String, String ) -> Http.Metadata
meta status headers =
    { url = Discussions.firstPageUrl, statusCode = status, statusText = "", headers = Dict.fromList headers }


replies : Test
replies =
    describe "readPage"
        [ test "a page and the next one" <|
            \_ ->
                Discussions.readPage (Http.GoodStatus_ (meta 200 [ ( "link", "<https://x/?page=2>; rel=\"next\"" ) ]) fixture)
                    |> Result.map (\p -> ( List.map .number p.discussions, p.next ))
                    |> Expect.equal (Ok ( [ 3, 4, 5 ], Just "https://x/?page=2" ))
        , test "the rate limit, with its reset" <|
            \_ ->
                Discussions.readPage (Http.BadStatus_ (meta 403 [ ( "X-RateLimit-Remaining", "0" ), ( "X-RateLimit-Reset", "1794100000" ) ]) "")
                    |> Expect.equal (Err (RateLimited (Just 1794100000)))
        , test "a 403 that is not the rate limit" <|
            \_ ->
                Discussions.readPage (Http.BadStatus_ (meta 403 [ ( "x-ratelimit-remaining", "12" ) ]) "")
                    |> Expect.equal (Err (Unavailable "GitHub replied 403"))
        , test "a reply that is not JSON" <|
            \_ ->
                Discussions.readPage (Http.GoodStatus_ (meta 200 []) "<html>")
                    |> Expect.equal (Err (Unavailable "GitHub's reply could not be read"))
        , test "no network" <|
            \_ -> Discussions.readPage Http.NetworkError_ |> Expect.equal (Err (Unavailable "GitHub could not be reached"))
        ]
