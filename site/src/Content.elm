module Content exposing
    ( Style(..)
    , load
    , none
    , view
    )

{-| The site's prose, written as Markdown in `content/` and rendered with dillonkearns/elm-markdown
into the site's own classes.

A page's data reads its file with `load`, which fails the build if the Markdown does not parse or
uses an HTML element this renderer does not know. The page's view renders it with `view`:

  - `{{name}}` is replaced by the value of `name` in `vars`: a count or a version that comes from
    the page's data. A name not in `vars` is left as it is.
  - The paragraphs that open the page (after its `#` title, if any) are its lede.
  - With the `Site` style, each `##` heading starts a section.
  - `<slot name="x"></slot>` places the Elm view `x` of `slots`: a table, buttons, anything computed.
  - `<button-link href="/standard" text="Text"></button-link>` is a button; with `quiet="true"`, a
    quiet one. `<actions>` around buttons sets them in a row.
  - `<note class="sd-draft-note">...</note>` is a block of Markdown in a box of that class.

A link whose address starts with `http` opens in a new tab.

-}

import BackendTask exposing (BackendTask)
import BackendTask.File
import Dict exposing (Dict)
import FatalError exposing (FatalError)
import Html exposing (Html)
import Html.Attributes as Attr
import Markdown.Block as Block exposing (Block)
import Markdown.Html
import Markdown.Parser
import Markdown.Renderer exposing (Renderer)


{-| The two looks of the site: the test suite's pages (`ts-` classes), and the pages of the book and
its mechanisation (`sd-` classes).
-}
type Style
    = Site
    | Book


{-| The text of `content/<name>.md`, checked: it parses, and it uses no HTML element the renderer
does not know.
-}
load : String -> BackendTask FatalError String
load name =
    let
        path =
            "content/" ++ name ++ ".md"
    in
    BackendTask.File.rawFile path
        |> BackendTask.allowFatal
        |> BackendTask.andThen
            (\text ->
                case Markdown.Parser.parse text of
                    Err deadEnds ->
                        BackendTask.fail
                            (FatalError.fromString
                                (path ++ ": the Markdown does not parse: " ++ String.join "; " (List.map Markdown.Parser.deadEndToString deadEnds))
                            )

                    Ok blocks ->
                        case Markdown.Renderer.render (renderer Site Dict.empty False) blocks of
                            Err problem ->
                                BackendTask.fail (FatalError.fromString (path ++ ": " ++ problem))

                            Ok _ ->
                                BackendTask.succeed text
            )


{-| No variables and no slots.
-}
none : { vars : Dict String String, slots : Dict String (Html msg) }
none =
    { vars = Dict.empty, slots = Dict.empty }


{-| The Markdown rendered, with its `{{name}}` variables and its slots filled in.
-}
view : Style -> { vars : Dict String String, slots : Dict String (Html msg) } -> String -> List (Html msg)
view style { vars, slots } text =
    let
        filled =
            Dict.foldl (\name value acc -> String.replace ("{{" ++ name ++ "}}") value acc) text vars
    in
    case Markdown.Parser.parse filled of
        Err _ ->
            [ Html.p [] [ Html.text "(This text could not be read.)" ] ]

        Ok blocks ->
            let
                ( lede, rest ) =
                    splitLede blocks

                render isLede bs =
                    Markdown.Renderer.render (renderer style slots isLede) bs
                        |> Result.withDefault []
            in
            render True lede
                ++ (case style of
                        Site ->
                            sections rest |> List.map (\group -> Html.section [ Attr.class "ts-section" ] (render False group))

                        Book ->
                            render False rest
                   )


{-| The page's opening: its `#` title and the paragraphs that follow it, up to the first block of
another kind; and the rest.
-}
splitLede : List Block -> ( List Block, List Block )
splitLede blocks =
    let
        go acc bs =
            case bs of
                ((Block.Heading Block.H1 _) as b) :: more ->
                    go (b :: acc) more

                ((Block.Paragraph _) as b) :: more ->
                    go (b :: acc) more

                _ ->
                    ( List.reverse acc, bs )
    in
    go [] blocks


{-| The blocks in groups, each starting at a `##` heading (but the first, which starts where the
lede ends).
-}
sections : List Block -> List (List Block)
sections blocks =
    let
        isH2 b =
            case b of
                Block.Heading Block.H2 _ ->
                    True

                _ ->
                    False

        go current acc bs =
            case bs of
                [] ->
                    List.reverse (close current acc)

                b :: more ->
                    if isH2 b then
                        go [ b ] (close current acc) more

                    else
                        go (b :: current) acc more

        close current acc =
            if List.isEmpty current then
                acc

            else
                List.reverse current :: acc
    in
    go [] [] blocks


renderer : Style -> Dict String (Html msg) -> Bool -> Renderer (Html msg)
renderer style slots isLede =
    let
        default =
            Markdown.Renderer.defaultHtmlRenderer

        classes =
            case style of
                Site ->
                    { h1 = "ts-h1", h2 = "ts-h2", h3 = "sd-h3", lede = "ts-lede" }

                Book ->
                    { h1 = "sd-chapter-title", h2 = "sd-h sd-h1", h3 = "sd-h3", lede = "sd-lede" }
    in
    { default
        | heading =
            \{ level, children } ->
                case level of
                    Block.H1 ->
                        Html.h1 [ Attr.class classes.h1 ] children

                    Block.H2 ->
                        Html.h2 [ Attr.class classes.h2 ] children

                    Block.H3 ->
                        Html.h3 [ Attr.class classes.h3 ] children

                    Block.H4 ->
                        Html.h4 [] children

                    Block.H5 ->
                        Html.h5 [] children

                    Block.H6 ->
                        Html.h6 [] children
        , paragraph =
            Html.p
                [ Attr.class
                    (if isLede then
                        classes.lede

                     else
                        "sd-p"
                    )
                ]
        , link =
            \{ title, destination } children ->
                Html.a
                    (Attr.href destination
                        :: (case title of
                                Just t ->
                                    [ Attr.title t ]

                                Nothing ->
                                    []
                           )
                        ++ (if String.startsWith "http" destination then
                                [ Attr.target "_blank", Attr.rel "noopener noreferrer" ]

                            else
                                []
                           )
                    )
                    children
        , codeBlock =
            \{ body, language } ->
                Html.pre
                    [ Attr.class
                        (if language == Just "lean" then
                            "sd-pre sd-lean"

                         else
                            "sd-pre"
                        )
                    ]
                    [ Html.code [] [ Html.text (String.trimRight body) ] ]
        , table = \children -> Html.div [ Attr.class "sd-table-wrap" ] [ Html.table [ Attr.class "ts-table" ] children ]
        , html =
            Markdown.Html.oneOf
                [ Markdown.Html.tag "slot"
                    (\name _ -> Dict.get name slots |> Maybe.withDefault (Html.text ""))
                    |> Markdown.Html.withAttribute "name"
                , Markdown.Html.tag "button-link"
                    (\href text quiet _ ->
                        Html.a
                            [ Attr.class
                                (if quiet == Just "true" then
                                    "sd-button sd-button-quiet"

                                 else
                                    "sd-button"
                                )
                            , Attr.href href
                            ]
                            [ Html.text text ]
                    )
                    |> Markdown.Html.withAttribute "href"
                    |> Markdown.Html.withAttribute "text"
                    |> Markdown.Html.withOptionalAttribute "quiet"
                , Markdown.Html.tag "note"
                    (\class children -> Html.div [ Attr.class (class ++ " sd-note") ] children)
                    |> Markdown.Html.withAttribute "class"
                , Markdown.Html.tag "actions"
                    (\children -> Html.div [ Attr.class "sd-actions" ] children)
                ]
    }
