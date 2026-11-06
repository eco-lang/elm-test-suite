module Style exposing (styleNode)

{-| The site's stylesheet, as global elm-css snippets for the `ts-` classes the views use.
-}

import Css
import Css.Global exposing (Snippet)
import Html
import Html.Styled



-- DESIGN TOKENS


colors =
    { accent = "#4CAF50"
    , accentDark = "#2E7D32"
    , text = "#1C1917"
    , heading = "#44403C"
    , muted = "#78716C"
    , border = "#DDD8CE"
    , bg = "#FDFCFA"
    , bgWhite = "#FFFFFF"
    , bgSubtle = "#F7F4EF"
    , bgCode = "#1E1E1E"
    , codeText = "#E8E8E8"
    , pass = "#2E7D32"
    , passBg = "#E8F5E9"
    , fail = "#C62828"
    , failBg = "#FDECEA"
    , skip = "#8D6E63"
    , skipBg = "#F0EDE7"
    , missing = "#9E9890"
    }


fontHeading : String
fontHeading =
    "Montserrat, sans-serif"


fontBody : String
fontBody =
    "Inter, system-ui, sans-serif"


fontCode : String
fontCode =
    "'Roboto Mono', ui-monospace, monospace"



-- STYLE NODE


styleNode : Html.Html msg
styleNode =
    Css.Global.global style
        |> Html.Styled.toUnstyled


style : List Snippet
style =
    List.concat
        [ baseStyles
        , layoutStyles
        , typographyStyles
        , tableStyles
        , statusStyles
        , barStyles
        , codeStyles
        , filterStyles
        , resultStyles
        ]


p : String -> String -> Css.Style
p =
    Css.property



-- BASE


baseStyles : List Snippet
baseStyles =
    [ Css.Global.selector "*, *::before, *::after" [ p "box-sizing" "border-box" ]
    , Css.Global.body
        [ p "margin" "0"
        , p "background-color" colors.bg
        , p "color" colors.text
        , p "font-family" fontBody
        , p "font-size" "15px"
        , p "line-height" "1.5"
        , p "-webkit-font-smoothing" "antialiased"
        ]
    , Css.Global.a
        [ p "color" colors.accentDark
        , p "text-decoration" "none"
        ]
    , Css.Global.selector "a:hover" [ p "text-decoration" "underline" ]
    ]



-- LAYOUT


layoutStyles : List Snippet
layoutStyles =
    [ Css.Global.class "ts-header"
        [ p "border-bottom" ("1px solid " ++ colors.border)
        , p "background-color" colors.bgWhite
        ]
    , Css.Global.class "ts-header-inner"
        [ p "max-width" "1200px"
        , p "margin" "0 auto"
        , p "padding" "14px 16px"
        , p "display" "flex"
        , p "align-items" "center"
        , p "gap" "24px"
        , p "flex-wrap" "wrap"
        ]
    , Css.Global.class "ts-brand"
        [ p "font-family" fontHeading
        , p "font-weight" "700"
        , p "font-size" "18px"
        , p "color" colors.text
        , p "display" "flex"
        , p "align-items" "center"
        , p "gap" "10px"
        ]
    , Css.Global.class "ts-brand-mark"
        [ p "display" "inline-block"
        , p "width" "14px"
        , p "height" "14px"
        , p "border-radius" "3px"
        , p "background-color" colors.accent
        , p "transform" "rotate(45deg)"
        ]
    , Css.Global.class "ts-nav"
        [ p "display" "flex"
        , p "gap" "18px"
        , p "font-weight" "500"
        , p "font-size" "14px"
        ]
    , Css.Global.selector ".ts-nav a" [ p "color" colors.heading ]
    , Css.Global.class "ts-main"
        [ p "max-width" "1200px"
        , p "margin" "0 auto"
        , p "padding" "28px 16px 48px"
        ]
    , Css.Global.class "ts-footer"
        [ p "border-top" ("1px solid " ++ colors.border)
        , p "color" colors.muted
        , p "font-size" "13px"
        ]
    , Css.Global.class "ts-footer-inner"
        [ p "max-width" "1200px"
        , p "margin" "0 auto"
        , p "padding" "18px 16px"
        , p "display" "flex"
        , p "gap" "8px 24px"
        , p "flex-wrap" "wrap"
        ]
    , Css.Global.class "ts-section" [ p "margin-top" "36px" ]
    , Css.Global.class "ts-card"
        [ p "background-color" colors.bgWhite
        , p "border" ("1px solid " ++ colors.border)
        , p "border-radius" "8px"
        , p "padding" "16px 18px"
        ]
    , Css.Global.class "ts-cards"
        [ p "display" "grid"
        , p "grid-template-columns" "repeat(auto-fill, minmax(250px, 1fr))"
        , p "gap" "14px"
        ]
    , Css.Global.class "ts-scroll" [ p "overflow-x" "auto" ]
    , Css.Global.class "ts-crumbs"
        [ p "font-size" "14px"
        , p "color" colors.muted
        , p "margin-bottom" "8px"
        ]
    ]



-- TYPOGRAPHY


typographyStyles : List Snippet
typographyStyles =
    [ Css.Global.class "ts-h1"
        [ p "font-family" fontHeading
        , p "font-weight" "700"
        , p "font-size" "28px"
        , p "line-height" "1.25"
        , p "margin" "0 0 8px"
        , p "word-break" "break-word"
        ]
    , Css.Global.class "ts-h2"
        [ p "font-family" fontHeading
        , p "font-weight" "600"
        , p "font-size" "20px"
        , p "margin" "0 0 12px"
        , p "color" colors.heading
        ]
    , Css.Global.class "ts-h3"
        [ p "font-family" fontHeading
        , p "font-weight" "600"
        , p "font-size" "16px"
        , p "margin" "0"
        ]
    , Css.Global.class "ts-lede"
        [ p "color" colors.heading
        , p "max-width" "760px"
        , p "margin" "0 0 4px"
        ]
    , Css.Global.class "ts-muted" [ p "color" colors.muted ]
    , Css.Global.class "ts-small" [ p "font-size" "13px" ]
    , Css.Global.class "ts-big-number"
        [ p "font-family" fontHeading
        , p "font-weight" "700"
        , p "font-size" "26px"
        , p "font-variant-numeric" "tabular-nums"
        ]
    ]



-- TABLES


tableStyles : List Snippet
tableStyles =
    [ Css.Global.class "ts-table"
        [ p "width" "100%"
        , p "border-collapse" "collapse"
        , p "background-color" colors.bgWhite
        , p "border" ("1px solid " ++ colors.border)
        , p "border-radius" "8px"
        , p "font-size" "14px"
        ]
    , Css.Global.selector ".ts-table th"
        [ p "text-align" "left"
        , p "font-weight" "600"
        , p "color" colors.heading
        , p "background-color" colors.bgSubtle
        , p "padding" "8px 10px"
        , p "border-bottom" ("1px solid " ++ colors.border)
        , p "white-space" "nowrap"
        , p "position" "sticky"
        , p "top" "0"
        ]
    , Css.Global.selector ".ts-table td"
        [ p "padding" "7px 10px"
        , p "border-bottom" ("1px solid " ++ colors.border)
        , p "vertical-align" "top"
        ]
    , Css.Global.selector ".ts-table tr:last-child td" [ p "border-bottom" "none" ]
    , Css.Global.selector ".ts-table tbody tr:hover td" [ p "background-color" colors.bgSubtle ]
    , Css.Global.class "ts-num"
        [ p "text-align" "right"
        , p "font-variant-numeric" "tabular-nums"
        , p "white-space" "nowrap"
        ]
    , Css.Global.class "ts-center" [ p "text-align" "center" ]
    , Css.Global.class "ts-test-name"
        [ p "font-family" fontCode
        , p "font-size" "13px"
        , p "word-break" "break-all"
        ]
    , Css.Global.class "ts-summary"
        [ p "color" colors.muted
        , p "font-size" "13px"
        , p "margin-top" "2px"
        ]
    ]



-- STATUS


statusStyles : List Snippet
statusStyles =
    [ Css.Global.class "ts-badge"
        [ p "display" "inline-block"
        , p "padding" "1px 8px"
        , p "border-radius" "999px"
        , p "font-size" "12px"
        , p "font-weight" "600"
        , p "white-space" "nowrap"
        , p "line-height" "18px"
        ]
    , Css.Global.class "ts-pass" [ p "color" colors.pass, p "background-color" colors.passBg ]
    , Css.Global.class "ts-fail" [ p "color" colors.fail, p "background-color" colors.failBg ]
    , Css.Global.class "ts-skip" [ p "color" colors.skip, p "background-color" colors.skipBg ]
    , Css.Global.class "ts-missing" [ p "color" colors.missing, p "background-color" colors.bgSubtle ]
    , Css.Global.class "ts-text-pass" [ p "color" colors.pass ]
    , Css.Global.class "ts-text-fail" [ p "color" colors.fail ]
    , Css.Global.class "ts-text-skip" [ p "color" colors.skip ]
    ]



-- PASS/FAIL BARS


barStyles : List Snippet
barStyles =
    [ Css.Global.class "ts-bar"
        [ p "display" "flex"
        , p "height" "8px"
        , p "border-radius" "4px"
        , p "overflow" "hidden"
        , p "background-color" colors.bgSubtle
        , p "min-width" "80px"
        , p "margin-top" "4px"
        ]
    , Css.Global.class "ts-bar-pass" [ p "background-color" colors.accent ]
    , Css.Global.class "ts-bar-fail" [ p "background-color" colors.fail ]
    , Css.Global.class "ts-bar-skip" [ p "background-color" colors.skip ]
    ]



-- CODE


codeStyles : List Snippet
codeStyles =
    [ Css.Global.class "ts-pre"
        [ p "font-family" fontCode
        , p "font-size" "12.5px"
        , p "line-height" "1.55"
        , p "background-color" colors.bgCode
        , p "color" colors.codeText
        , p "border-radius" "6px"
        , p "padding" "12px 14px"
        , p "margin" "8px 0 0"
        , p "overflow" "auto"
        , p "max-height" "480px"
        , p "white-space" "pre"
        ]
    , Css.Global.class "ts-doc"
        [ p "white-space" "pre-wrap"
        , p "font-size" "14px"
        , p "color" colors.heading
        , p "margin" "0"
        , p "font-family" fontBody
        ]
    , Css.Global.class "ts-source"
        [ p "border-radius" "6px"
        , p "overflow" "auto"
        , p "max-height" "720px"
        , p "font-size" "12.5px"
        ]
    , Css.Global.selector ".ts-source pre.elmsh"
        [ p "margin" "0"
        , p "padding" "12px 14px"
        , p "font-family" fontCode
        , p "line-height" "1.55"
        ]
    , Css.Global.selector ".ts-source code" [ p "font-family" fontCode ]
    , Css.Global.selector ".elmsh-line::before"
        [ p "content" "attr(data-elmsh-lc)"
        , p "display" "inline-block"
        , p "text-align" "right"
        , p "width" "32px"
        , p "padding-right" "16px"
        , p "opacity" "0.35"
        ]
    , Css.Global.selector "details > summary"
        [ p "cursor" "pointer"
        , p "color" colors.heading
        , p "font-size" "13px"
        , p "font-weight" "500"
        , p "margin-top" "8px"
        ]
    ]



-- FILTERS


filterStyles : List Snippet
filterStyles =
    [ Css.Global.class "ts-filters"
        [ p "display" "flex"
        , p "gap" "8px"
        , p "flex-wrap" "wrap"
        , p "align-items" "center"
        , p "margin" "16px 0"
        ]
    , Css.Global.class "ts-chip"
        [ p "border" ("1px solid " ++ colors.border)
        , p "background-color" colors.bgWhite
        , p "color" colors.heading
        , p "border-radius" "999px"
        , p "padding" "4px 12px"
        , p "font-size" "13px"
        , p "font-family" fontBody
        , p "cursor" "pointer"
        ]
    , Css.Global.class "ts-chip-active"
        [ p "background-color" colors.text
        , p "border-color" colors.text
        , p "color" colors.bgWhite
        ]
    , Css.Global.class "ts-input"
        [ p "border" ("1px solid " ++ colors.border)
        , p "border-radius" "6px"
        , p "padding" "5px 10px"
        , p "font-size" "14px"
        , p "font-family" fontBody
        , p "min-width" "220px"
        , p "flex" "1 1 220px"
        , p "max-width" "360px"
        ]
    ]



-- PER-COMPILER RESULTS


resultStyles : List Snippet
resultStyles =
    [ Css.Global.class "ts-results"
        [ p "display" "grid"
        , p "gap" "14px"
        ]

    -- A grid item is as wide as its widest line unless allowed to shrink; the <pre> then scrolls.
    , Css.Global.selector ".ts-results > *" [ p "min-width" "0" ]
    , Css.Global.class "ts-result-head"
        [ p "display" "flex"
        , p "align-items" "center"
        , p "gap" "10px"
        , p "flex-wrap" "wrap"
        ]
    , Css.Global.class "ts-result-fail" [ p "border-left" ("4px solid " ++ colors.fail) ]
    , Css.Global.class "ts-result-pass" [ p "border-left" ("4px solid " ++ colors.accent) ]
    , Css.Global.class "ts-result-skip" [ p "border-left" ("4px solid " ++ colors.skip) ]
    , Css.Global.class "ts-result-missing" [ p "border-left" ("4px solid " ++ colors.missing) ]
    ]
