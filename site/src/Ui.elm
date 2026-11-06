module Ui exposing (bar, countsCell, percent, statusBadge, statusBadgeWithReason)

{-| Small view pieces shared by the pages.
-}

import Data exposing (Counts, Status(..))
import Html exposing (Html)
import Html.Attributes as Attr


statusClass : Status -> String
statusClass status =
    "ts-" ++ Data.statusLabel status


statusBadge : Status -> Html msg
statusBadge status =
    Html.span [ Attr.class ("ts-badge " ++ statusClass status) ] [ Html.text (Data.statusLabel status) ]


{-| A badge whose tooltip is the reason for a failure or skip.
-}
statusBadgeWithReason : Status -> String -> Html msg
statusBadgeWithReason status reason =
    Html.span
        [ Attr.class ("ts-badge " ++ statusClass status)
        , Attr.title reason
        ]
        [ Html.text (Data.statusLabel status) ]


{-| A pass/fail/skip bar, its segments sized by count.
-}
bar : Counts -> Html msg
bar counts =
    let
        total =
            counts.pass + counts.fail + counts.skip

        segment cls n =
            if n == 0 then
                Html.text ""

            else
                Html.span
                    [ Attr.class cls
                    , Attr.style "width" (String.fromFloat (100 * toFloat n / toFloat (max 1 total)) ++ "%")
                    ]
                    []
    in
    Html.div [ Attr.class "ts-bar" ]
        [ segment "ts-bar-pass" counts.pass
        , segment "ts-bar-fail" counts.fail
        , segment "ts-bar-skip" counts.skip
        ]


percent : Counts -> String
percent counts =
    let
        run =
            counts.pass + counts.fail
    in
    if run == 0 then
        "–"

    else
        String.fromFloat (toFloat (round (1000 * toFloat counts.pass / toFloat run)) / 10) ++ "%"


{-| "passed / failed / skipped", coloured, with a bar under it.
-}
countsCell : Counts -> List (Html msg)
countsCell counts =
    [ Html.span [ Attr.class "ts-text-pass" ] [ Html.text (String.fromInt counts.pass) ]
    , Html.text " / "
    , Html.span
        [ Attr.class
            (if counts.fail > 0 then
                "ts-text-fail"

             else
                "ts-muted"
            )
        ]
        [ Html.text (String.fromInt counts.fail) ]
    , if counts.skip > 0 then
        Html.span [ Attr.class "ts-text-skip" ] [ Html.text (" / " ++ String.fromInt counts.skip) ]

      else
        Html.text ""
    , bar counts
    ]
