port module StandardA84DuplicatePortNameTest exposing (main)

{-| Two ports of one program may not have the same name.

A Standard Definition of Elm?, ruling A84: the name of every port of a program is distinct from
those of its other ports (and of the platform's managers); a program that breaks this does not
elaborate. <https://elm-test-suite.netlify.app/standard/restrictions/modules-program> <https://elm-test-suite.netlify.app/standard/rules/p-stat-module>

This module and `StandardA84PortsHelper` both declare a port `send`. Elm 0.19.1 compiles the program;
it stops when it starts, as the two ports collide at run time.

-}

-- TAGS: elm19-bug
-- COMPILE-ERROR: two ports named send in one program
-- CHECK: {{-- [A-Z ]+ -}}

import StandardA84PortsHelper


port send : String -> Cmd msg


main : Program () () ()
main =
    Platform.worker
        { init = \_ -> ( (), Cmd.batch [ send "one", StandardA84PortsHelper.send "two" ] )
        , update = \_ model -> ( model, Cmd.none )
        , subscriptions = \_ -> Sub.none
        }
