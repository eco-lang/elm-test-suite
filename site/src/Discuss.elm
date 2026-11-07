module Discuss exposing
    ( Category(..)
    , Target
    , categoryFromSlug
    , categoryName
    , categorySlug
    , categoryUrl
    , newDiscussionUrl
    , repo
    , searchUrl
    )

{-| Links to the GitHub Discussions of the repository, where the Definition and the tests are
discussed. A discussion is about an item of the site when its title holds the item's key in square
brackets, `[r:d-atexp-var] ...`; the links here start such discussions and find them. See
`plans/github-discussions.md`.
-}

import Url.Builder


{-| The repository whose Discussions the site uses.
-}
repo : String
repo =
    "eco-lang/elm-test-suite"


type Category
    = Standard
    | Tests


categorySlug : Category -> String
categorySlug category =
    case category of
        Standard ->
            "standard"

        Tests ->
            "tests"


categoryName : Category -> String
categoryName category =
    case category of
        Standard ->
            "Standard"

        Tests ->
            "Tests"


categoryFromSlug : String -> Maybe Category
categoryFromSlug slug =
    if slug == categorySlug Standard then
        Just Standard

    else if slug == categorySlug Tests then
        Just Tests

    else
        Nothing


{-| What a page is about, for its Discussions section and its links.

  - `key`: the key that a discussion about the item carries in its title (`r:d-atexp-var`).
  - `noun`: what the item is, for "Discuss this rule".
  - `url`: the item's full address on the site, which a new discussion links back to.
  - `context`: a line or two for a new discussion: the edition of the Definition, or the outcomes
    of a test.

-}
type alias Target =
    { category : Category
    , key : String
    , noun : String
    , url : String
    , context : String
    }


github : List String -> List Url.Builder.QueryParameter -> String
github path query =
    Url.Builder.crossOrigin "https://github.com" (String.split "/" repo ++ path) query


categoryUrl : Category -> String
categoryUrl category =
    github [ "discussions", "categories", categorySlug category ] []


{-| GitHub's form for a new discussion in the item's category, its title starting with the item's
key and its body linking back to the item.
-}
newDiscussionUrl : Target -> String
newDiscussionUrl target =
    github [ "discussions", "new" ]
        [ Url.Builder.string "category" (categorySlug target.category)
        , Url.Builder.string "title" ("[" ++ target.key ++ "] ")
        , Url.Builder.string "body" (body target)
        ]


body : Target -> String
body target =
    String.join "\n\n"
        [ "About " ++ target.url
        , target.context
        , "<!-- Keep [" ++ target.key ++ "] in the title: the site shows this discussion on that page. -->"
        , ""
        ]


{-| GitHub's search of the repository's discussions for the item's key, which finds the
discussions about it without the site's help.
-}
searchUrl : String -> String
searchUrl key =
    github [ "discussions" ] [ Url.Builder.string "discussions_q" ("\"" ++ key ++ "\"") ]
