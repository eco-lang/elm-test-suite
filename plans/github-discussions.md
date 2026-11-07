# Plan: link the site with GitHub Discussions

## Goal

Every citable part of *The Definition of Standard Elm* on the site (a rule, restriction, derived
form or entry of the basis), and every test of the suite, should be a place where people can start
and find a debate. The debates live in the Discussions of this repository,
[eco-lang/elm-test-suite](https://github.com/eco-lang/elm-test-suite/discussions), which are
enabled. The site links to them and shows the discussions about each item on its page, live,
without a server, a token or a rebuild.

## What GitHub allows

Checked against the API on 2026-11-07:

- `GET https://api.github.com/repos/eco-lang/elm-test-suite/discussions` lists discussions without
  authentication: number, title, body, author, category (name and slug), labels, comment count,
  reactions, accepted answer, `html_url`, created and updated times. It pages 100 at a time (`Link`
  header).
- `GET .../discussions/{number}/comments` lists the comments of one, also without authentication.
- Both send `Access-Control-Allow-Origin: *`, so the site's Elm code can call them from the
  browser.
- Unauthenticated calls are limited to 60 an hour per IP address.
- The GraphQL API needs a token even to read, and the discussion pages on github.com cannot be read
  across origins. Neither is used.
- Writing (starting a discussion, commenting) needs a signed-in GitHub user. The site links to
  GitHub for that.

The repository has one discussion now (the welcome post, category Announcements) and GitHub's
default categories.

## Decisions

1. **Repository:** eco-lang/elm-test-suite.
2. **Categories:** two new categories, both in the open-ended discussion format:
   - *Standard* (slug `standard`): discussions about the Definition;
   - *Tests* (slug `tests`): discussions about the tests and their results under each compiler.

   The site reads only these two. The other categories are left alone.
3. **Key:** a discussion is about an item when its title contains the item's key in square
   brackets: `[r:d-atexp-var] Should a variable ...`. A title may carry several keys (a discussion
   about two rules, or a rule and the test that checks it). Matching uses titles, not GitHub
   labels: only maintainers can set labels, while anyone can write a title. The keys are:

   | Key | Item | Category |
   |-----|------|----------|
   | `r:<label>` | a rule | Standard |
   | `res:`, `df:`, `b:` | a restriction, derived form, entry of the basis | Standard |
   | `ch:<chapter>` | a chapter, for what is not about one item | Standard |
   | `t:<project>/<Test>` | a test, as in its address: `t:elm-bugs/CompilerIssue2281LongLineListTest` | Tests |
   | `p:<project>` | a test project as a whole | Tests |

   The labels of the Definition are stable by design (`definition/README.md`), so a discussion
   stays attached to its item across editions. A test's key is its project and module name, which
   change only when a test is renamed or moved.
4. **The site's address** is `Site.canonicalUrl` (`site/app/Site.elm`), now
   `https://elm-test-suite.netlify.app`. The prefilled discussions link back to items through it,
   so a change of address is made there once. Discussions already posted keep the old links; the
   keys in their titles, not the links, attach them to items.

## Phase 1: links (static)

No JavaScript; works for every reader and for search engines.

- A new module `site/src/Discuss.elm` (shared by the book and the test pages):
  - `repo : String`; `type Category = Standard | Tests` and its slug.
  - `newDiscussionUrl : { category : Category, key : String, address : String, context : String } -> String`
    builds `https://github.com/eco-lang/elm-test-suite/discussions/new?category=<slug>&title=...&body=...`
    with the title `[<key>] ` (the reader completes it) and a body that links back to the item at
    `Site.canonicalUrl ++ address` and gives its context: the edition of the Definition, or for a
    test the compilers and their outcomes when the page was built. All parts URL-encoded
    (`Url.percentEncode`).
  - `searchUrl : String -> String` builds
    `https://github.com/eco-lang/elm-test-suite/discussions?discussions_q=...` for the key, so a
    reader without JavaScript can still find existing discussions.
- Rule pages (`Route/Standard/Rules/Rule_.elm`) and item pages (`Standard/ItemView.elm`): a
  "Discuss this rule" (or restriction, ...) action next to "Read it in its chapter", and a "See
  discussions on GitHub" link.
- Chapter pages: "Discuss this chapter" at the foot, keyed `[ch:<slug>]`.
- Test pages (`Route/Projects/Project_/Test_.elm`): "Discuss this test", keyed
  `[t:<project>/<Test>]`, in the Tests category. Project pages: "Discuss this project", keyed
  `[p:<project>]`.
- On the book pages these links are static and go inside `View.freeze` with the rest of the page.
- The front page of the book and the results page each get a short paragraph on how to take part,
  linking to their category.

Check before building: that the `title`, `body` and `category` query parameters of
`/discussions/new` prefill as expected on this repository, and how they combine with a discussion
form if one is added (see Repository setup).

## Phase 2: the live panel (dynamic, in the browser)

- **Fetching, once per visit.** `Shared` (`site/app/Shared.elm`) gets
  `discussions : Discussions`, where

  ```elm
  type Discussions
      = NotAsked
      | Loading
      | Loaded (Dict String (List Discussion)) -- by key
      | Failed Problem -- rate limit, network, unexpected reply
  ```

  It starts the fetch the first time the reader is on a page that shows discussions (a book page,
  a project page or a test page), from `Shared.init` or on a page change. One fetch serves both
  categories: it follows the `Link` header's `next` page until the list ends, keeps the
  discussions of categories `standard` and `tests`, and indexes them by every key in their titles.
  Client-side navigation keeps the shared model, so a reader who visits many pages makes one or a
  few requests in all.
- **Decoding.** `Discussions` (new module): the `Discussion` record (number, title without its
  keys, category, author login and avatar, comment count, answered, updated time, `html_url`), its
  decoder, and `keysOf : String -> List String`, which reads the `[prefix:label]` keys of a title.
  Unknown prefixes are ignored.
- **The panel.** A view `Discussions.panel : String -> Discussions -> Html msg` for a key,
  rendered by rule, item, chapter, project and test pages (on the book pages *outside*
  `View.freeze`), from `Shared.Model` (the view of every route receives it, so the routes stay
  stateless). A project page also lists the discussions about its tests. It shows:
  - while loading, a quiet "Loading discussions";
  - the discussions about the key, newest activity first: title (linking to GitHub), author, number
    of replies, an "answered" mark, last activity;
  - none: "No discussions yet" and the Phase 1 link to start one;
  - failure: "Discussions could not be loaded" and the search link. When GitHub reports its rate
    limit (status 403 or 429 with `x-ratelimit-remaining: 0`), say so and when it resets.
- **What stays out of the pages' data.** The discussions are fetched by the browser and are not
  in `content.dat`; the frozen book content is unchanged.
- **Discussions pages.** `/standard/discussions` lists every discussion of the Standard category,
  and `/discussions` every discussion of the Tests category, each grouped by the item it is about,
  with the most active items first. Their shells are pre-rendered and their lists are filled in
  from `Shared`, as the panel is. They are linked from the book's front page and the results page.

Freshness: GitHub's API is cached for about a minute, so a new discussion appears on the site
within a minute or two of being posted. Nothing is rebuilt.

## Phase 3: later, if wanted

- **Replies on the site.** Expand a discussion to show its comments, fetched on demand from
  `.../discussions/{number}/comments`; this needs route state for the expanded threads. Rendering
  the comment bodies needs their Markdown (the API returns Markdown, not HTML).
- **Counts in the lists.** Discussion counts in the rules, restrictions, derived forms and basis
  lists. Those tables are frozen; the counts would be a small unfrozen column or a badge added next
  to each row from the shared data.
- **A build-time snapshot** of the discussions in the pages, for search engines and readers
  without JavaScript, refreshed live as above.
- **Counts in the results.** A discussion count beside each test in the project tables and in the
  list of tests whose outcome differs.
- **Posting from the site.** Needs GitHub sign-in (OAuth) and so a server: elm-pages with the
  Netlify adapter, server-side sessions, CSRF protection. Only if leaving the site to post turns
  out to be a real obstacle.

## Repository setup (by a maintainer, on GitHub)

1. Create the categories, both in the open-ended discussion format:
   - *Standard* (slug `standard`), described as, say, "The Definition of Standard Elm: one
     discussion per rule or question, with the rule's key in the title, as the site's Discuss links
     write it";
   - *Tests* (slug `tests`), described as, say, "The tests and their results: one discussion per
     test or project, with its key in the title".

   GitHub makes the slug from the name; if it differs, the site's `Discuss.Category` slugs follow
   it.
2. Optionally, discussion forms `.github/DISCUSSION_TEMPLATE/standard.yml` and `tests.yml` asking
   for the item, the edition or compiler, and the argument. Check that the site's prefilled title
   survives them.
3. Pin a short post in each category explaining the title convention and linking to the site.

## Testing

- `keysOf` and the URL builders: unit tests (elm-test in `site/`, or checks in a small script),
  including several keys in a title, keys with dots (`b:Platform.Cmd.none`) and slashes
  (`t:elm-bugs/CompilerIssue2281LongLineListTest`), and titles without keys.
- The decoder against a saved reply of the API (a fixture under `site/`), including a discussion in
  another category and one with no keys.
- In the browser: a page with discussions, one without, a failed fetch (block `api.github.com`),
  the rate limit (a reply with `x-ratelimit-remaining: 0`), and client-side navigation between
  rule pages making no further requests.
- The pages still build and render with JavaScript off, showing the Phase 1 links.

## Files

| File | Change |
|------|--------|
| `site/src/Discuss.elm` | new: repository, categories, discussion and search URLs |
| `site/src/Discussions.elm` | new: types, decoder, `keysOf`, the panel |
| `site/app/Shared.elm` | the discussions in the shared model; fetch on the first page that shows them |
| `site/app/Route/Standard/Rules/Rule_.elm`, `site/src/Standard/ItemView.elm`, `site/app/Route/Standard/Chapter_.elm` | Discuss links (frozen) and the panel (unfrozen) |
| `site/app/Route/Projects/Project_.elm`, `site/app/Route/Projects/Project_/Test_.elm` | Discuss links and the panel |
| `site/app/Route/Standard/Discussions.elm`, `site/app/Route/Discussions.elm` | new: the discussions pages |
| `site/app/Route/Standard.elm`, `site/app/Route/Index.elm` | how to take part; links to the discussions pages |
| `site/src/Style.elm` | styles of the panel and the actions |
| `definition/README.md`, `README.md` | the title convention and how the site uses Discussions |

## Settled

1. Both categories use the open-ended discussion format.
2. Tests get their own category, *Tests*, in the same phases as the Definition.
3. The site's address is `https://elm-test-suite.netlify.app` (`Site.canonicalUrl`, corrected
   from `https://eco-lang.github.io/elm-test-suite`). It may change; it is set in one place.
