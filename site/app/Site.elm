module Site exposing (canonicalUrl, config, socialImage, title)

import BackendTask exposing (BackendTask)
import FatalError exposing (FatalError)
import Head
import Head.Seo as Seo
import MimeType
import Pages.Url
import SiteConfig exposing (SiteConfig)
import SiteUrl


title : String
title =
    "Elm Exactly"


{-| The site's address, from SITE_URL at build time (scripts/site-url.mjs): the production site,
or the staging site on a staging build.
-}
canonicalUrl : String
canonicalUrl =
    SiteUrl.siteUrl


{-| The image of every page's link preview (Open Graph and Twitter card): the Elm tangram's pieces
around the site's name, 1200 by 630, in `public/og.png`. Its address is absolute, as link preview
readers require.
-}
socialImage : Seo.Image
socialImage =
    { url = Pages.Url.external (canonicalUrl ++ "/og.png")
    , alt = "Elm Exactly: does every Elm compiler fit the same pieces together?"
    , dimensions = Just { width = 1200, height = 630 }
    , mimeType = Just (MimeType.Image MimeType.Png)
    }


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
