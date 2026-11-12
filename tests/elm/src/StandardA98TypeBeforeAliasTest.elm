module StandardA98TypeBeforeAliasTest exposing (main)

{-| A custom type may mention a local alias declared after it, even one spelt like an imported type.

The module declares `type T = T String` and then `type alias String = Int`. A Standard Definition
of Elm?, ruling A98: a module's type declarations are elaborated together (rule r:sm-topdec-types),
and rule r:sm-topdec-seq does not split them, so `String` in `T`'s constructor is the local alias
and `T : Int -> T`, whatever the order of the two declarations. Reading the declarations in order
would make `T`'s argument the imported `String`, and `n + 1` would not type-check.
<https://elm-test-suite.netlify.app/standard/rules/sm-topdec-types>

Elm 0.19.1, 0.19.2 and 0.19.3 compile the program.

-}

-- TAGS: elm-spec, sm-topdec-types, sm-topdec-seq, sm-typbind, sm-datbind
-- CHECK: field (T 3): 4

import Html exposing (text)


type T
    = T String


type alias String =
    Int


field : T -> Int
field (T n) =
    n + 1


main =
    let
        _ =
            Debug.log "field (T 3)" (field (T 3))
    in
    text "done"
