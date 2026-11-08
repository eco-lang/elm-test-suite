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


fontBook : String
fontBook =
    "'Source Serif 4', Georgia, 'Times New Roman', serif"


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
        , standardStyles
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
        , p "transform" "rotate(45deg)"
        ]
    , Css.Global.class "ts-github"
        [ p "margin-left" "auto"
        , p "display" "flex"
        , p "align-items" "center"
        , p "color" colors.heading
        ]
    , Css.Global.selector ".ts-github:hover" [ p "color" colors.accentDark ]
    , Css.Global.class "ts-github-mark" [ p "width" "22px", p "height" "22px" ]
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



-- A STANDARD DEFINITION OF ELM?


standardStyles : List Snippet
standardStyles =
    [ Css.Global.class "sd-book"
        [ p "font-family" fontBook
        , p "font-size" "17px"
        , p "line-height" "1.6"
        , p "max-width" "880px"
        , p "margin" "0 auto"
        ]
    , Css.Global.selector ".sd-book .katex" [ p "font-size" "1.08em" ]
    , Css.Global.class "sd-title"
        [ p "font-weight" "700"
        , p "font-size" "36px"
        , p "line-height" "1.2"
        , p "text-align" "center"
        , p "margin" "24px 0 6px"
        ]
    , Css.Global.class "sd-edition" [ p "text-align" "center", p "color" colors.heading, p "font-size" "18px" ]
    , Css.Global.class "sd-author" [ p "text-align" "center", p "color" colors.muted, p "margin-bottom" "28px" ]
    , Css.Global.class "sd-lede" [ p "color" colors.heading ]
    , Css.Global.class "sd-licence"
        [ p "margin-top" "40px"
        , p "padding-top" "12px"
        , p "border-top" ("1px solid " ++ colors.border)
        , p "font-size" "13px"
        , p "color" colors.muted
        ]
    , Css.Global.class "sd-draft-note"
        [ p "background-color" "#FFF8E1"
        , p "border-left" "4px solid #F9A825"
        , p "padding" "10px 14px"
        , p "border-radius" "4px"
        , p "font-size" "15px"
        ]
    , Css.Global.class "sd-actions" [ p "display" "flex", p "gap" "12px", p "flex-wrap" "wrap", p "margin" "20px 0 8px" ]
    , Css.Global.class "sd-button"
        [ p "font-family" fontBody
        , p "font-size" "14px"
        , p "font-weight" "600"
        , p "padding" "8px 16px"
        , p "border-radius" "999px"
        , p "background-color" colors.accentDark
        , p "color" colors.bgWhite
        ]
    , Css.Global.selector ".sd-button:hover" [ p "text-decoration" "none", p "background-color" colors.text ]
    , Css.Global.class "sd-button-quiet"
        [ p "background-color" colors.bgWhite
        , p "color" colors.heading
        , p "border" ("1px solid " ++ colors.border)
        ]
    , Css.Global.selector ".sd-button-quiet:hover" [ p "background-color" colors.bgSubtle ]
    , Css.Global.class "sd-contents-head" [ p "font-size" "24px", p "margin" "36px 0 8px" ]
    , Css.Global.class "sd-contents-sub" [ p "font-size" "19px", p "margin" "24px 0 8px" ]
    , Css.Global.class "sd-contents" [ p "list-style" "none", p "padding" "0", p "margin" "0" ]
    , Css.Global.class "sd-contents-chapter"
        [ p "padding" "10px 0"
        , p "border-bottom" ("1px solid " ++ colors.border)
        ]
    , Css.Global.class "sd-contents-title" [ p "font-weight" "600", p "font-size" "18px", p "color" colors.text ]
    , Css.Global.class "sd-contents-rules" [ p "margin-left" "12px", p "font-family" fontBody, p "font-size" "13px" ]
    , Css.Global.class "sd-contents-sections"
        [ p "list-style" "none"
        , p "padding" "0"
        , p "margin" "4px 0 0 2.2em"
        , p "font-size" "15px"
        , p "columns" "2 300px"
        , p "column-gap" "28px"
        ]
    , Css.Global.selector ".sd-contents-sections a" [ p "color" colors.heading ]
    , Css.Global.class "sd-num"
        [ p "display" "inline-block"
        , p "min-width" "2.2em"
        , p "font-variant-numeric" "tabular-nums"
        , p "color" colors.muted
        , p "font-weight" "600"
        ]
    , Css.Global.class "sd-chapter-title"
        [ p "font-size" "32px"
        , p "line-height" "1.25"
        , p "margin" "6px 0 18px"
        , p "display" "flex"
        , p "align-items" "baseline"
        , p "gap" "4px 14px"
        , p "flex-wrap" "wrap"
        ]
    , Css.Global.selector ".sd-chapter-title .sd-num" [ p "min-width" "0", p "color" colors.accentDark ]
    , Css.Global.class "sd-edition-chip"
        [ p "font-family" fontBody
        , p "font-size" "11px"
        , p "font-weight" "600"
        , p "margin-left" "8px"
        , p "padding" "1px 8px"
        , p "border-radius" "999px"
        , p "background-color" "#FFF8E1"
        , p "color" "#8D6E00"
        ]
    , Css.Global.class "sd-toc"
        [ p "background-color" colors.bgWhite
        , p "border" ("1px solid " ++ colors.border)
        , p "border-radius" "8px"
        , p "padding" "10px 18px"
        , p "font-size" "15px"
        , p "margin-bottom" "24px"
        ]
    , Css.Global.selector ".sd-toc ol" [ p "list-style" "none", p "padding" "0", p "margin" "0", p "columns" "2 280px" ]
    , Css.Global.selector ".sd-toc a" [ p "color" colors.heading ]
    , Css.Global.class "sd-p" [ p "margin" "0 0 0.85em" ]
    , Css.Global.class "sd-h" [ p "line-height" "1.3", p "position" "relative" ]
    , Css.Global.class "sd-h1" [ p "font-size" "24px", p "margin" "1.8em 0 0.6em" ]
    , Css.Global.class "sd-h2" [ p "font-size" "19px", p "margin" "1.5em 0 0.5em" ]
    , Css.Global.class "sd-h3" [ p "font-size" "17px", p "margin" "1.2em 0 0.4em" ]
    , Css.Global.class "sd-pilcrow"
        [ p "margin-left" "8px"
        , p "color" colors.border
        , p "font-weight" "400"
        , p "opacity" "0"
        ]
    , Css.Global.selector ".sd-h:hover .sd-pilcrow" [ p "opacity" "1" ]
    , Css.Global.selector ".sd-pilcrow:hover" [ p "color" colors.accentDark, p "text-decoration" "none" ]
    , Css.Global.selector ":target" [ p "scroll-margin-top" "16px" ]
    , Css.Global.selector ".sd-rule:target, .sd-figure:target, .sd-h:target"
        [ p "background-color" "#FFF8E1"
        , p "box-shadow" "0 0 0 6px #FFF8E1"
        , p "border-radius" "2px"
        ]
    , Css.Global.class "sd-display" [ p "overflow-x" "auto", p "overflow-y" "hidden", p "margin" "0.4em 0 1em" ]
    , Css.Global.class "sd-kw" [ p "font-family" fontCode, p "font-size" "0.86em" ]
    , Css.Global.class "sd-ref" [ p "white-space" "nowrap" ]
    , Css.Global.class "sd-ref-missing" [ p "color" colors.fail ]
    , Css.Global.class "sd-raw"
        [ p "color" colors.fail
        , p "font-family" fontCode
        , p "font-size" "0.85em"
        , p "white-space" "pre-wrap"
        ]
    , Css.Global.class "sd-list" [ p "margin" "0 0 0.85em", p "padding-left" "1.6em" ]
    , Css.Global.selector ".sd-list > li > .sd-p:last-child" [ p "margin-bottom" "0.3em" ]
    , Css.Global.class "sd-quote" [ p "margin" "0.6em 0 1em 2em" ]
    , Css.Global.class "sd-center" [ p "text-align" "center" ]
    , Css.Global.selector ".sd-center .sd-table-wrap" [ p "display" "flex", p "justify-content" "center" ]
    , Css.Global.class "sd-right" [ p "text-align" "right" ]
    , Css.Global.class "sd-minipage" [ p "display" "inline-block", p "vertical-align" "top", p "margin" "0 12px" ]

    -- Rules and rule groups.
    , Css.Global.class "sd-rulegroup"
        [ p "display" "flex"
        , p "justify-content" "space-between"
        , p "align-items" "center"
        , p "flex-wrap" "wrap"
        , p "gap" "8px 16px"
        , p "margin" "2em 0 0.6em"
        , p "padding-bottom" "6px"
        , p "border-bottom" ("1px solid " ++ colors.border)
        ]
    , Css.Global.class "sd-rulegroup-title" [ p "font-weight" "700", p "font-size" "18px" ]
    , Css.Global.class "sd-judgement"
        [ p "border" ("1px solid " ++ colors.heading)
        , p "padding" "2px 10px"
        , p "max-width" "100%"
        , p "overflow-x" "auto"
        ]
    , Css.Global.class "sd-rule"
        [ p "display" "flex"
        , p "align-items" "center"
        , p "gap" "12px"
        , p "margin" "0.3em 0"
        ]
    , Css.Global.class "sd-rule-math" [ p "flex" "1 1 auto", p "min-width" "0", p "overflow-x" "auto", p "overflow-y" "hidden" ]
    , Css.Global.selector ".sd-rule-math .katex-display" [ p "margin" "0.5em 0" ]

    -- KaTeX centres display mathematics as a block, so a formula wider than its box overflows on
    -- both sides and its left part cannot be scrolled to. As an inline block in a centred line it
    -- is centred when it fits and overflows to the right when it does not.
    , Css.Global.selector ".sd-rule-math .katex-display, .sd-display .katex-display" [ p "text-align" "center" ]
    , Css.Global.selector ".sd-rule-math .katex-display > .katex, .sd-display .katex-display > .katex"
        [ p "display" "inline-block"
        , p "text-align" "left"
        ]
    , Css.Global.class "sd-rule-num"
        [ p "flex" "0 0 auto"
        , p "font-variant-numeric" "tabular-nums"
        , p "color" colors.heading
        , p "min-width" "3em"
        , p "text-align" "right"
        ]
    , Css.Global.class "sd-rule-single"
        [ p "background-color" colors.bgWhite
        , p "border" ("1px solid " ++ colors.border)
        , p "border-radius" "8px"
        , p "padding" "8px 18px"
        , p "margin" "16px 0"
        ]
    , Css.Global.class "sd-item-chip"
        [ p "font-family" fontCode
        , p "font-size" "12px"
        , p "color" colors.muted
        , p "border" ("1px solid " ++ colors.border)
        , p "border-radius" "4px"
        , p "padding" "0 5px"
        , p "margin-left" "6px"
        , p "white-space" "nowrap"
        , p "text-decoration" "none"
        ]
    , Css.Global.selector ".sd-item-chip:hover" [ p "color" colors.accentDark, p "border-color" colors.accentDark ]
    , Css.Global.selector "li.sd-item > .sd-p:last-of-type" [ p "display" "inline" ]
    , Css.Global.class "sd-item-cell" [ p "vertical-align" "top", p "padding-left" "8px" ]
    , Css.Global.class "sd-item-meta" [ p "color" colors.muted, p "margin" "4px 0 20px" ]
    , Css.Global.class "sd-item-place" [ p "margin-bottom" "18px" ]
    , Css.Global.class "sd-item-source" [ p "margin-top" "-4px" ]
    , Css.Global.class "sd-also" [ p "color" colors.muted, p "font-size" "15px" ]

    -- Discussions (DiscussionsView)
    , Css.Global.class "dz-section"
        [ p "margin-top" "32px"
        , p "padding" "16px 20px"
        , p "border" ("1px solid " ++ colors.border)
        , p "border-radius" "8px"
        , p "background-color" colors.bgWhite
        ]
    , Css.Global.class "dz-head" [ p "font-size" "18px", p "margin" "0 0 10px", p "color" colors.heading ]
    , Css.Global.class "dz-status" [ p "color" colors.muted, p "margin" "6px 0" ]
    , Css.Global.class "dz-failed" [ p "color" colors.fail ]
    , Css.Global.class "dz-list" [ p "list-style" "none", p "padding" "0", p "margin" "6px 0" ]
    , Css.Global.class "dz-entry" [ p "padding" "8px 0", p "border-bottom" ("1px solid " ++ colors.bgSubtle) ]
    , Css.Global.selector ".dz-entry:last-child" [ p "border-bottom" "none" ]
    , Css.Global.class "dz-meta" [ p "font-size" "13px", p "color" colors.muted, p "margin-top" "2px" ]
    , Css.Global.class "dz-answered" [ p "color" colors.pass, p "font-weight" "600" ]
    , Css.Global.class "dz-key" [ p "font-family" fontCode, p "font-size" "12px" ]
    , Css.Global.class "dz-actions" [ p "margin" "12px 0 4px", p "font-size" "15px", p "font-weight" "600" ]
    , Css.Global.class "dz-sep" [ p "color" colors.muted, p "margin" "0 8px", p "font-weight" "400" ]
    , Css.Global.class "dz-note" [ p "font-size" "13px", p "color" colors.muted, p "margin" "4px 0 0" ]
    , Css.Global.class "dz-group" [ p "margin" "20px 0" ]
    , Css.Global.class "dz-group-head"
        [ p "font-size" "15px"
        , p "margin" "0 0 4px"
        , p "display" "flex"
        , p "align-items" "baseline"
        , p "gap" "8px"
        ]
    , Css.Global.class "dz-count"
        [ p "font-size" "12px"
        , p "color" colors.muted
        , p "background-color" colors.bgSubtle
        , p "border-radius" "999px"
        , p "padding" "0 7px"
        ]
    , Css.Global.class "sd-nowrap" [ p "white-space" "nowrap", p "vertical-align" "top" ]
    , Css.Global.class "sd-basis-row" [ p "display" "flex", p "gap" "12px", p "margin" "6px 0", p "align-items" "baseline" ]
    , Css.Global.class "sd-basis-label" [ p "flex" "0 0 56px", p "color" colors.muted, p "font-size" "14px" ]
    , Css.Global.class "sd-basis-names" [ p "display" "flex", p "flex-wrap" "wrap", p "gap" "6px 14px" ]
    , Css.Global.class "sd-basis-name" [ p "font-family" fontCode, p "font-size" "14px" ]
    , Css.Global.class "sd-rule-slug"
        [ p "font-family" fontCode
        , p "font-size" "16px"
        , p "font-weight" "400"
        , p "color" colors.heading
        , p "background-color" colors.bgSubtle
        , p "padding" "2px 8px"
        , p "border-radius" "4px"
        ]
    , Css.Global.class "sd-rule-actions"
        [ p "display" "flex"
        , p "gap" "10px"
        , p "flex-wrap" "wrap"
        , p "font-family" fontBody
        , p "font-size" "13px"
        ]
    , Css.Global.class "sd-comments" [ p "font-size" "15.5px", p "margin" "0.6em 0 1.4em" ]
    , Css.Global.class "sd-comments-head" [ p "font-style" "italic", p "margin-bottom" "4px" ]
    , Css.Global.class "sd-comment"
        [ p "display" "grid"
        , p "grid-template-columns" "3.4em 1fr"
        , p "gap" "4px"
        ]
    , Css.Global.class "sd-comment-num" [ p "font-variant-numeric" "tabular-nums" ]
    , Css.Global.selector ".sd-comment-body .sd-p" [ p "margin-bottom" "0.6em" ]

    -- Figures and tables.
    , Css.Global.class "sd-figure"
        [ p "margin" "1.6em 0"
        , p "padding" "12px 0 8px"
        , p "border-top" ("1px solid " ++ colors.border)
        , p "border-bottom" ("1px solid " ++ colors.border)
        ]
    , Css.Global.class "sd-figure-body" [ p "overflow-x" "auto", p "font-size" "15.5px" ]
    , Css.Global.selector ".sd-figure-body > .sd-table-wrap" [ p "display" "flex", p "justify-content" "center" ]
    , Css.Global.selector ".sd-figure-body > .sd-p" [ p "margin" "0.6em 0 0.2em" ]
    , Css.Global.selector ".sd-figure figcaption"
        [ p "text-align" "center"
        , p "font-size" "15px"
        , p "margin-top" "10px"
        , p "color" colors.heading
        ]
    , Css.Global.class "sd-figure-num" [ p "font-weight" "600", p "color" colors.heading ]
    , Css.Global.class "sd-table-wrap" [ p "overflow-x" "auto", p "margin" "0.4em 0" ]
    , Css.Global.class "sd-table" [ p "border-collapse" "collapse" ]
    , Css.Global.selector ".sd-table td"
        [ p "padding" "2px 10px"
        , p "vertical-align" "top"
        , p "white-space" "nowrap"
        , p "text-align" "left"
        ]
    , Css.Global.selector ".sd-table td.sd-wrap" [ p "white-space" "normal", p "min-width" "9em" ]
    , Css.Global.selector ".sd-table tr.sd-rule-above > td" [ p "border-top" ("1px solid " ++ colors.heading) ]
    , Css.Global.selector ".sd-table.sd-rule-below tr:last-child > td" [ p "border-bottom" ("1px solid " ++ colors.heading) ]
    , Css.Global.class "sd-pre"
        [ p "font-family" fontCode
        , p "font-size" "13px"
        , p "background-color" colors.bgSubtle
        , p "padding" "10px 14px"
        , p "border-radius" "6px"
        , p "overflow-x" "auto"
        ]

    -- Paging between chapters and rules.
    , Css.Global.class "sd-pager"
        [ p "display" "flex"
        , p "justify-content" "space-between"
        , p "gap" "16px"
        , p "margin-top" "48px"
        , p "padding-top" "16px"
        , p "border-top" ("1px solid " ++ colors.border)
        ]
    , Css.Global.class "sd-pager-link" [ p "display" "flex", p "flex-direction" "column", p "max-width" "48%" ]
    , Css.Global.selector ".sd-pager-link:last-child" [ p "text-align" "right", p "margin-left" "auto" ]
    , Css.Global.class "sd-pager-label"
        [ p "font-family" fontBody
        , p "font-size" "12px"
        , p "text-transform" "uppercase"
        , p "letter-spacing" "0.04em"
        , p "color" colors.muted
        ]
    , Css.Global.selector ".sd-rules-table td" [ p "font-family" fontBody ]
    , Css.Global.selector ".sd-pager .sd-num" [ p "min-width" "0", p "margin-right" "0.4em" ]
    ]
