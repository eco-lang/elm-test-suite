module LibraryTest exposing (suite)

{-| The core library values the translator evaluates (plans/library-elm-texts.md): the closure of a
module's texts, the library modules it writes, and test programs that name library values.
-}

import Expect exposing (Expectation)
import Test exposing (Test, describe, test)
import Translate.Directives as Directives
import Translate.Library as Library exposing (Library)
import Translate.LibraryTexts as LibraryTexts
import Translate.Parse as Parse
import Translate.Pipeline as Pipeline exposing (Outcome(..))


{-| A small List module in elm/core's form: a kernel `cons`, texts that name each other, and `sum`,
whose scheme quantifies a `number` variable.
-}
listText : String
listText =
    """module List exposing (singleton, map, foldl, foldr, length, reverse, sum, head)

import Basics exposing (..)
import Elm.Kernel.List
import Maybe exposing ( Maybe(..) )


infix right 5 (::) = cons


singleton : a -> List a
singleton value =
  [value]


cons : a -> List a -> List a
cons =
  Elm.Kernel.List.cons


map : (a -> b) -> List a -> List b
map f xs =
  foldr (\\x acc -> cons (f x) acc) [] xs


foldl : (a -> b -> b) -> b -> List a -> b
foldl func acc list =
  case list of
    [] ->
      acc

    x :: xs ->
      foldl func (func x acc) xs


foldr : (a -> b -> b) -> b -> List a -> b
foldr fn acc ls =
  foldl fn acc (reverse ls)


length : List a -> Int
length xs =
  foldl (\\_ i -> i + 1) 0 xs


reverse : List a -> List a
reverse list =
  foldl cons [] list


sum : List number -> number
sum numbers =
  foldl (+) 0 numbers


head : List a -> Maybe a
head list =
  case list of
    x :: xs ->
      Just x

    [] ->
      Nothing
"""


tupleText : String
tupleText =
    """module Tuple exposing (pair, first, second)


pair : a -> b -> (a, b)
pair a b =
  (a, b)


first : (a, b) -> a
first (x,_) =
  x


second : (a, b) -> b
second (_,y) =
  y
"""


texts : List ( Library.Text, String )
texts =
    [ ( { modul = "List", path = "List.elm", values = [ "foldl", "head", "length", "map", "sum" ] }, listText )
    , ( { modul = "Tuple", path = "Tuple.elm", values = [ "first", "second" ] }, tupleText )
    ]


built : Result String { library : Library, lean : String }
built =
    LibraryTexts.build texts


libraryContaining : List String -> Expectation
libraryContaining fragments =
    case built of
        Ok b ->
            Expect.all
                (List.map
                    (\f lean ->
                        if String.contains f lean then
                            Expect.pass

                        else
                            Expect.fail ("expected `" ++ f ++ "` in:\n" ++ lean)
                    )
                    fragments
                )
                b.lean

        Err e ->
            Expect.fail ("the library is refused: " ++ e)


lib : Library
lib =
    built |> Result.map .library |> Result.withDefault Library.empty


runIn : Library -> String -> Outcome
runIn l source =
    Pipeline.translateIn l (\_ -> Nothing) { project = "elm", name = "T", defName = "g" } source (Directives.read source)


{-| A test program logging `x` with the given expression.
-}
logging : String -> String -> String
logging expected e =
    "module T exposing (main)\n-- TAGS: elm-spec\n-- CHECK: x: " ++ expected ++ "\nimport Html exposing (text)\n\nmain =\n    let\n        _ =\n            Debug.log \"x\" (" ++ e ++ ")\n    in\n    text \"done\"\n"


translatedIn : Library -> List String -> String -> Expectation
translatedIn l fragments source =
    case runIn l source of
        Translated t ->
            Expect.all
                (List.map
                    (\f lean ->
                        if String.contains f lean then
                            Expect.pass

                        else
                            Expect.fail ("expected `" ++ f ++ "` in:\n" ++ lean)
                    )
                    fragments
                )
                t.lean

        Refused r ->
            Expect.fail ("refused: " ++ r.reason ++ " " ++ Maybe.withDefault "" r.detail)


suite : Test
suite =
    describe "the core library"
        [ describe "closure"
            [ test "map needs foldr, cons, and through them foldl and reverse, in the file's order" <|
                \_ ->
                    case Parse.parse listText of
                        Ok file ->
                            Expect.equal [ "cons", "map", "foldl", "foldr", "reverse" ] (Library.closure file [ "map" ])

                        Err _ ->
                            Expect.fail "does not parse"
            , test "a value whose text names no other is alone" <|
                \_ ->
                    case Parse.parse listText of
                        Ok file ->
                            Expect.equal [ "head" ] (Library.closure file [ "head" ])

                        Err _ ->
                            Expect.fail "does not parse"
            ]
        , describe "the library modules"
            [ test "cons is the list constructor, written (::)" <|
                \_ -> libraryContaining [ ".fn \"cons\" [] (.atexp (.op \"::\"))" ]
            , test "sum has its default copy at Float and a copy at Int, both exposed" <|
                \_ ->
                    libraryContaining
                        [ ".fn \"sum\" [pv \"numbers\"] (ap (v \"foldl\") [.atexp (.op \"+\"), .atexp (.scon (.intF 0)), v \"numbers\"])"
                        , ".fn \"sum$Int\" [pv \"numbers\"] (ap (v \"foldl\") [.atexp (.op \"+\"), i 0, v \"numbers\"])"
                        , ".var \"sum\", .var \"sum$Int\""
                        ]
            , test "the kernel import is left out, the others kept; no value outside the closure" <|
                \_ ->
                    case built of
                        Ok b ->
                            Expect.all
                                [ \t -> Expect.equal False (String.contains "Elm.Kernel" t)
                                , \t -> Expect.equal True (String.contains "⟨\"Maybe\", \"Maybe\", some (.items [.opened \"Maybe\"])⟩" t)
                                , \t -> Expect.equal False (String.contains "singleton" t)
                                , \t -> Expect.equal False (String.contains "\"pair\"" t)
                                , \t -> Expect.equal True (String.contains "def libTexts : List ModSrc :=\n  [libText_List, libText_Tuple]" t)
                                ]
                                b.lean

                        Err e ->
                            Expect.fail e
            , test "a text that names another kernel value is refused" <|
                \_ ->
                    case LibraryTexts.build [ ( { modul = "Tuple", path = "Tuple.elm", values = [ "first" ] }, "module Tuple exposing (first)\n\nimport Elm.Kernel.Utils\n\nfirst : (a, b) -> a\nfirst p =\n  Elm.Kernel.Utils.first p\n" ) ] of
                        Ok _ ->
                            Expect.fail "built"

                        Err e ->
                            Expect.equal True (String.startsWith "kernel:Elm.Kernel.Utils.first" e)
            ]
        , describe "programs"
            [ test "a library value is refused without the library" <|
                \_ ->
                    case runIn Library.empty (logging "1" "Tuple.first ( 1, 2 )") of
                        Refused r ->
                            Expect.equal "basis:Tuple.first" r.reason

                        Translated _ ->
                            Expect.fail "translated"
            , test "with it, a qualified library value is a value of the basis, and recorded" <|
                \_ ->
                    case runIn lib (logging "1" "Tuple.first ( 1, \"a\" )") of
                        Translated t ->
                            Expect.all
                                [ \_ -> Expect.equal [ "Tuple.first" ] t.library
                                , \_ -> Expect.equal True (String.contains "library := [\"Tuple.first\"]" t.lean)
                                , \_ -> Expect.equal True (String.contains "ap (qv \"Tuple\" \"first\")" t.lean)
                                ]
                                ()

                        Refused r ->
                            Expect.fail ("refused: " ++ r.reason ++ " " ++ Maybe.withDefault "" r.detail)
            , test "List.sum at Int is its copy sum$Int" <|
                \_ -> translatedIn lib [ "qv \"List\" \"sum$Int\"", "chk .check \"x: 3\" .int" ] (logging "3" "List.sum [ 1, 2 ] // 1")
            , test "List.sum at Float is sum itself" <|
                \_ -> translatedIn lib [ "ap (qv \"List\" \"sum\")", "(.scon (.intF 1))" ] (logging "1.5" "List.sum [ 1, 0.5 ]")
            , test "an exposed library value is written unqualified, and its import exposes its copies" <|
                \_ ->
                    translatedIn lib
                        [ "ap (v \"sum$Int\")", ".var \"sum\", .var \"sum$Int\"" ]
                        "module T exposing (main)\n-- TAGS: elm-spec\n-- CHECK: x: 3\nimport Html exposing (text)\nimport List exposing (sum)\n\nmain =\n    let\n        _ =\n            Debug.log \"x\" (sum [ 1, 2 ] // 1)\n    in\n    text \"done\"\n"
            , test "a library value that the translator does not evaluate is still refused" <|
                \_ ->
                    case runIn lib (logging "[1]" "List.singleton 1") of
                        Refused r ->
                            Expect.equal "basis:List.singleton" r.reason

                        Translated _ ->
                            Expect.fail "translated"
            ]
        ]
