# Vendored library sources

Unmodified copies of the elm/core 1.0.5 and elm/json 1.1.3 sources that the test basis of the
Lean mechanisation reads (plans/lean-full-definition/step-09-static-semantics.md, section 6;
plans/core-library.md). Each package keeps its own LICENSE (BSD-3-Clause, Copyright Evan
Czaplicki). Only the modules whose values the tests use are copied:

| Package | Modules |
|---------|---------|
| elm/core 1.0.5 | Array, List, Maybe, Result, String, Tuple |
| elm/json 1.1.3 | Json.Encode |

`definition/tools/src/Translate.elm` reads the annotations of the library values the tests use
from these files and writes them to `StandardElmMech/Generated/StaticLibrary.lean`.
