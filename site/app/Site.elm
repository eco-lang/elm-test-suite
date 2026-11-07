module Site exposing (canonicalUrl, config, title)

import BackendTask exposing (BackendTask)
import FatalError exposing (FatalError)
import Head
import SiteConfig exposing (SiteConfig)


title : String
title =
    "Elm Exactly"


canonicalUrl : String
canonicalUrl =
    "https://elm-test-suite.netlify.app"


config : SiteConfig
config =
    { canonicalUrl = canonicalUrl
    , head = head
    }


head : BackendTask FatalError (List Head.Tag)
head =
    [ Head.metaName "viewport" (Head.raw "width=device-width,initial-scale=1")
    , Head.metaName "description" (Head.raw "Results of the Elm compiler end-to-end test suite under each Elm compiler")
    ]
        |> BackendTask.succeed
