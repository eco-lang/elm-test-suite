module Icons exposing (elmTangram, github)

{-| The site's two icons, as inline SVG.
-}

import Html exposing (Html)
import VirtualDom


svgNs : String
svgNs =
    "http://www.w3.org/2000/svg"


svg : String -> String -> List (Html msg) -> Html msg
svg cls viewBox children =
    VirtualDom.nodeNS svgNs
        "svg"
        [ VirtualDom.attribute "class" cls
        , VirtualDom.attribute "viewBox" viewBox
        , VirtualDom.attribute "aria-hidden" "true"
        , VirtualDom.attribute "focusable" "false"
        ]
        children


polygon : String -> String -> Html msg
polygon fill points =
    VirtualDom.nodeNS svgNs "polygon" [ VirtualDom.attribute "fill" fill, VirtualDom.attribute "points" points ] []


{-| The seven pieces of the Elm tangram, in its four colours.
-}
elmTangram : String -> Html msg
elmTangram cls =
    svg cls
        "0 0 323.3 323.3"
        [ polygon "#F0AD00" "161.649,152.782 231.514,82.916 91.783,82.916"
        , polygon "#7FD13B" "8.867,0 79.241,70.375 232.213,70.375 161.838,0"
        , polygon "#7FD13B" "246.999,85.162 323.137,161.299 246.652,237.784 170.514,161.646"
        , polygon "#60B5CC" "323.298,143.724 323.298,0 179.573,0"
        , polygon "#5A6378" "152.781,161.649 0,8.868 0,314.432"
        , polygon "#F0AD00" "255.522,246.655 323.298,314.432 323.298,178.879"
        , polygon "#60B5CC" "161.649,170.517 8.869,323.298 314.43,323.298"
        ]


{-| The GitHub mark (Octicons, MIT licence), drawn in the current text colour.
-}
github : String -> Html msg
github cls =
    svg cls
        "0 0 16 16"
        [ VirtualDom.nodeNS svgNs
            "path"
            [ VirtualDom.attribute "fill" "currentColor"
            , VirtualDom.attribute "d" "M8 0C3.58 0 0 3.58 0 8c0 3.54 2.29 6.53 5.47 7.59.4.07.55-.17.55-.38 0-.19-.01-.82-.01-1.49-2.01.37-2.53-.49-2.69-.94-.09-.23-.48-.94-.82-1.13-.28-.15-.68-.52-.01-.53.63-.01 1.08.58 1.23.82.72 1.21 1.87.87 2.33.66.07-.52.28-.87.51-1.07-1.78-.2-3.64-.89-3.64-3.95 0-.87.31-1.59.82-2.15-.08-.2-.36-1.02.08-2.12 0 0 .67-.21 2.2.82.64-.18 1.32-.27 2-.27.68 0 1.36.09 2 .27 1.53-1.04 2.2-.82 2.2-.82.44 1.1.16 1.92.08 2.12.51.56.82 1.27.82 2.15 0 3.07-1.87 3.75-3.65 3.95.29.25.54.73.54 1.48 0 1.07-.01 1.93-.01 2.2 0 .21.15.46.55.38A8.013 8.013 0 0016 8c0-4.42-3.58-8-8-8z"
            ]
            []
        ]
