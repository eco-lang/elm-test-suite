/-
  A Standard Definition of Elm? Mechanisation, part 10.
  The example corpus.

  * `corpus`: 40 of the test programs that accompany the book, in this
    repository's tests/elm/src and tests/elm-core/src (<Name>.elm; each
    program's `source` names its folder). Each `Check` is one
    `Debug.log "label" (exp)` of the program, hand-translated into bare syntax
    through the derived-form functions of Derived.lean, with the value of the
    program's `-- CHECK: label: value` line, the value the test expects.
    Nothing reads the .elm files: when a test's CHECK lines change, its
    translation here must be changed by hand.
  * `rulings`: test programs of tests/elm-core/src and tests/elm/src that
    bear on the rulings A40 (Int overflow), A42 (division by zero), A43 (Int
    `^` with a negative exponent), A46 to A50 (float order, min, max and
    clamp, NaN equality) and A51 (function equality), with their CHECK values.
  * `coverage`: test programs for rules the corpus reaches only in passing,
    and for the examples given in the book's own Comments.

  Every example is a test program of this repository, and its expected values
  are its CHECK lines: the site's build compares the two and reports a
  difference. A check that expects no value (the program stops at
  Debug.todo) is written "(no value)"; its test has a CHECK-NOT line for the
  label and expects exit status 1.

  Top-level definitions of a module are placed in a `let` around the logged
  expression (grouped into components as for a let, which is what the module
  row of Appendix A does for definitions); the custom types' constructors are
  bound in the environment. Both stand in for Chapter 7 (out of scope).
  Where a program builds an operand from `List.length []` to defeat constant
  folding, the operand is written as the constant 0.
-/
import StandardElmMech.Basis
import StandardElmMech.Show

namespace StandardElm
open StandardElm.D

structure Check where
  label : String
  /-- The value of the CHECK line (the implementation's result). -/
  expected : String
  expr : Exp
  deriving Inhabited

structure Program where
  name : String
  /-- Where the implementation's result comes from. -/
  source : String := "tests/elm/src"
  cons : List (String × Nat) := []
  defs : List Def := []
  locals : List Def := []
  checks : List Check
  deriving Inhabited

/-- The phrase evaluated for a check: the program's definitions around
    `Debug.log "label" (exp)`. -/
def Program.phrase (p : Program) (ck : Check) : Exp :=
  letDefs p.defs (letDefs p.locals (debugLog ck.label ck.expr))

def Program.env (p : Program) : Env := E0with p.cons

def ck (label expected : String) (e : Exp) : Check := ⟨label, expected, e⟩

/-! ## Shorthands -/
def T : Exp := c "True"
def F : Exp := c "False"
def eq (a b : Exp) := bin "==" a b
def lst (ns : List Int) : Exp := listE (ns.map i)

/-! ## The corpus: 40 of the test programs that accompany the book -/

def pIntAdd : Program := {
  name := "IntAddTest", source := "tests/elm-core/src", checks := [
  ck "add1" "13" (bin "+" (i 10) (i 3)),
  ck "add2" "0" (bin "+" (i 5) (i (-5))),
  ck "add3" "-5" (bin "+" (i (-2)) (i (-3))) ] }

def pIntMul : Program := {
  name := "IntMulTest", source := "tests/elm-core/src", checks := [
  ck "mul1" "30" (bin "*" (i 10) (i 3)),
  ck "mul2" "-15" (bin "*" (i 5) (i (-3))),
  ck "mul3" "6" (bin "*" (i (-2)) (i (-3))),
  ck "mul4" "0" (bin "*" (i 0) (i 100)) ] }

def pIntDiv : Program := {
  name := "IntDivTest", source := "tests/elm-core/src", checks := [
  ck "div1" "3" (bin "//" (i 10) (i 3)),
  ck "div2" "-3" (bin "//" (i (-10)) (i 3)),
  ck "div3" "-3" (bin "//" (i 10) (i (-3))),
  ck "div4" "3" (bin "//" (i (-10)) (i (-3))) ] }

def pIntDivByZero : Program := {
  name := "IntDivByZeroTest", source := "tests/elm-core/src", checks := [
  ck "divZero1" "0" (bin "//" (i 10) (i 0)),
  ck "divZero2" "0" (bin "//" (i (-5)) (i 0)) ] }

def pIntModBy : Program := {
  name := "IntModByTest", source := "tests/elm-core/src", checks := [
  ck "mod1" "3" (ap (v "modBy") [i 4, i 7]),
  ck "mod2" "1" (ap (v "modBy") [i 4, i (-7)]),
  ck "mod3" "3" (ap (v "modBy") [i 4, i 7]),
  ck "mod4" "1" (ap (v "modBy") [i 4, i (-7)]),
  ck "mod5" "0" (ap (v "modBy") [i 5, i 0]) ] }

def pIntRemainderBy : Program := {
  name := "IntRemainderByTest", source := "tests/elm-core/src", checks := [
  ck "rem1" "3" (ap (v "remainderBy") [i 4, i 7]),
  ck "rem2" "-3" (ap (v "remainderBy") [i 4, i (-7)]),
  ck "rem3" "3" (ap (v "remainderBy") [i (-4), i 7]),
  ck "rem4" "-3" (ap (v "remainderBy") [i (-4), i (-7)]) ] }

def pIntPow : Program := {
  name := "IntPowTest", source := "tests/elm-core/src", checks := [
  ck "pow1" "8" (bin "^" (i 2) (i 3)),
  ck "pow2" "1" (bin "^" (i 5) (i 0)),
  ck "pow3" "1024" (bin "^" (i 2) (i 10)),
  ck "pow4" "-8" (bin "^" (.atexp (.paren (i (-2)))) (i 3)) ] }

def pIntNegate : Program := {
  name := "IntNegateTest", source := "tests/elm-core/src", checks := [
  ck "neg1" "-5" (ap (v "negate") [i 5]),
  ck "neg2" "5" (ap (v "negate") [i (-5)]),
  ck "neg3" "0" (ap (v "negate") [i 0]) ] }

def pIntAbs : Program := {
  name := "IntAbsTest", source := "tests/elm-core/src", checks := [
  ck "abs1" "5" (ap (v "abs") [i 5]),
  ck "abs2" "5" (ap (v "abs") [i (-5)]),
  ck "abs3" "0" (ap (v "abs") [i 0]) ] }

def pIntCompare : Program := {
  name := "IntCompareTest", source := "tests/elm-core/src", checks := [
  ck "lt" "True" (bin "<" (i 3) (i 10)),
  ck "gt" "True" (bin ">" (i 10) (i 3)),
  ck "le1" "True" (bin "<=" (i 3) (i 10)),
  ck "le2" "True" (bin "<=" (i 5) (i 5)),
  ck "ge1" "True" (bin ">=" (i 10) (i 3)),
  ck "ge2" "True" (bin ">=" (i 5) (i 5)),
  ck "eq" "True" (bin "==" (i 5) (i 5)),
  ck "ne" "True" (bin "/=" (i 5) (i 3)) ] }

def pIntMinMax : Program := {
  name := "IntMinMaxTest", source := "tests/elm-core/src", checks := [
  ck "min1" "3" (ap (v "min") [i 10, i 3]),
  ck "min2" "-5" (ap (v "min") [i (-5), i 5]),
  ck "max1" "10" (ap (v "max") [i 10, i 3]),
  ck "max2" "5" (ap (v "max") [i (-5), i 5]) ] }

def pBoolAnd : Program := {
  name := "BoolAndTest", checks := [
  ck "and1" "True" (andalso T T), ck "and2" "False" (andalso T F),
  ck "and3" "False" (andalso F T), ck "and4" "False" (andalso F F) ] }

def pBoolOr : Program := {
  name := "BoolOrTest", checks := [
  ck "or1" "True" (orelse T T), ck "or2" "True" (orelse T F),
  ck "or3" "True" (orelse F T), ck "or4" "False" (orelse F F) ] }

def pBoolNot : Program := {
  name := "BoolNotTest", source := "tests/elm-core/src", checks := [
  ck "not1" "False" (ap (v "not") [T]), ck "not2" "True" (ap (v "not") [F]) ] }

def pBoolXor : Program := {
  name := "BoolXorTest", source := "tests/elm-core/src", checks := [
  ck "xor1" "False" (ap (v "xor") [T, T]), ck "xor2" "True" (ap (v "xor") [T, F]),
  ck "xor3" "True" (ap (v "xor") [F, T]), ck "xor4" "False" (ap (v "xor") [F, F]) ] }

def pBoolShortCircuit : Program := {
  name := "BoolShortCircuitTest",
  defs := [
    .fn "stackBomb" [pv "n"] (bin "+" (i 1) (ap (v "stackBomb") [bin "+" (v "n") (i 1)])),
    .fn "shouldNotRun" [pw] (bin ">" (ap (v "stackBomb") [i 0]) (i 0)) ],
  checks := [
    ck "shortAnd" "False" (andalso F (ap (v "shouldNotRun") [.atexp .unit])),
    ck "shortOr" "True" (orelse T (ap (v "shouldNotRun") [.atexp .unit])) ] }

def pCompareChar : Program := {
  name := "CompareCharTest", source := "tests/elm-core/src", checks := [
  ck "cmp1" "LT" (ap (v "compare") [chA 'a', chA 'b']),
  ck "cmp2" "GT" (ap (v "compare") [chA 'z', chA 'a']),
  ck "cmp3" "EQ" (ap (v "compare") [chA 'x', chA 'x']) ] }

def pCompareEmptyList : Program := {
  name := "CompareEmptyListTest", source := "tests/elm-core/src",
  locals := [ .fn "emptyL" [] (.atexp .nil) ],
  checks := [
    ck "ee" "EQ" (ap (v "compare") [v "emptyL", v "emptyL"]),
    ck "ea" "LT" (ap (v "compare") [v "emptyL", lst [1]]),
    ck "ae" "GT" (ap (v "compare") [lst [1], v "emptyL"]),
    ck "eab" "LT" (ap (v "compare") [v "emptyL", lst [1, 2]]),
    ck "abe" "GT" (ap (v "compare") [lst [1, 2], v "emptyL"]),
    ck "aa" "EQ" (ap (v "compare") [lst [1], lst [1]]),
    ck "ab" "LT" (ap (v "compare") [lst [1], lst [2]]),
    ck "ba" "GT" (ap (v "compare") [lst [2], lst [1]]),
    ck "aba" "GT" (ap (v "compare") [lst [1, 2], lst [1]]) ] }

def pCompareTupleWithEmptyList : Program := {
  name := "CompareTupleWithEmptyListTest", source := "tests/elm-core/src",
  locals := [ .fn "emptyL" [] (.atexp .nil) ],
  checks := [
    ck "ee" "EQ" (ap (v "compare") [tup2 (i 0) (v "emptyL"), tup2 (i 0) (v "emptyL")]),
    ck "eA" "LT" (ap (v "compare") [tup2 (i 0) (v "emptyL"), tup2 (i 0) (lst [1])]),
    ck "Ae" "GT" (ap (v "compare") [tup2 (i 0) (lst [1]), tup2 (i 0) (v "emptyL")]),
    ck "eAB" "LT" (ap (v "compare") [tup2 (i 0) (v "emptyL"), tup2 (i 0) (lst [1, 2])]),
    ck "ABe" "GT" (ap (v "compare") [tup2 (i 0) (lst [1, 2]), tup2 (i 0) (v "emptyL")]),
    ck "f0_ee" "LT" (ap (v "compare") [tup2 (v "emptyL") (i 0), tup2 (lst [1]) (i 0)]),
    ck "f0_Ae" "GT" (ap (v "compare") [tup2 (lst [1]) (i 0), tup2 (v "emptyL") (i 0)]) ] }

def pEquality : Program := {
  name := "EqualityTest", source := "tests/elm-core/src", checks := [
  ck "eq1" "True" (eq (i 5) (i 5)),
  ck "eq2" "False" (eq (i 5) (i 6)),
  ck "ne1" "True" (bin "/=" (i 5) (i 6)),
  ck "ne2" "False" (bin "/=" (i 5) (i 5)),
  ck "listEq" "True" (eq (lst [1, 2, 3]) (lst [1, 2, 3])) ] }

def pEqualityBoolContainer : Program := {
  name := "EqualityBoolContainerTest", source := "tests/elm-core/src",
  locals := [ .fn "emptyBools" [] (.atexp .nil) ],
  checks := [
    ck "pairTT_TT" "True" (eq (tup2 T T) (tup2 T T)),
    ck "pairTT_TF" "False" (eq (tup2 T T) (tup2 T F)),
    ck "pairTF_TT" "False" (eq (tup2 T F) (tup2 T T)),
    ck "pairTF_FT" "False" (eq (tup2 T F) (tup2 F T)),
    ck "tripleTFT_TFT" "True" (eq (tup3 T F T) (tup3 T F T)),
    ck "tripleTFT_TFF" "False" (eq (tup3 T F T) (tup3 T F F)),
    ck "listTT_TT" "True" (eq (listE [T, T]) (listE [T, T])),
    ck "listTF_TF" "True" (eq (listE [T, F]) (listE [T, F])),
    ck "listTF_FT" "False" (eq (listE [T, F]) (listE [F, T])),
    ck "listTF_TT" "False" (eq (listE [T, F]) (listE [T, T])),
    ck "listEmpty" "True" (eq (v "emptyBools") (.atexp .nil)) ] }

def pEqualityBoolRecord : Program := {
  name := "EqualityBoolRecordTest", source := "tests/elm-core/src",
  locals := [
    .fn "ref" [] (recE [("a", T), ("b", F)]),
    .fn "sameAsRef" [] (recE [("a", T), ("b", F)]),
    .fn "flipA" [] (recE [("a", F), ("b", F)]),
    .fn "flipB" [] (recE [("a", T), ("b", T)]),
    .fn "flipBoth" [] (recE [("a", F), ("b", T)]),
    .fn "bothFalse" [] (recE [("a", F), ("b", F)]) ],
  checks := [
    ck "recEq" "True" (eq (v "ref") (v "sameAsRef")),
    ck "recDiffA" "False" (eq (v "ref") (v "flipA")),
    ck "recDiffB" "False" (eq (v "ref") (v "flipB")),
    ck "recDiffBoth" "False" (eq (v "ref") (v "flipBoth")),
    ck "recFF_FF" "True" (eq (v "bothFalse") (recE [("a", F), ("b", F)])) ] }

def pCaseCustomType : Program := {
  name := "CaseCustomTypeTest",
  cons := [("Circle", 1), ("Rectangle", 2)],
  defs := [ .fn "area" [pv "shape"] (caseOf (v "shape") [
    (pcon "Circle" [pv "r"], bin "*" (v "r") (v "r")),
    (pcon "Rectangle" [pv "w", pv "h"], bin "*" (v "w") (v "h")) ]) ],
  checks := [
    ck "shape1" "100" (ap (v "area") [ap (c "Circle") [i 10]]),
    ck "shape2" "50" (ap (v "area") [ap (c "Rectangle") [i 5, i 10]]) ] }

def pCaseListCons : Program := {
  name := "CaseListConsTest",
  defs := [ .fn "sumList" [pv "list"] (caseOf (v "list") [
    (P .nil, i 0),
    (.cons (P (pv "x")) (P (pv "xs")), bin "+" (v "x") (ap (v "sumList") [v "xs"])) ]) ],
  checks := [
    ck "sum1" "0" (ap (v "sumList") [.atexp .nil]),
    ck "sum2" "1" (ap (v "sumList") [lst [1]]),
    ck "sum3" "6" (ap (v "sumList") [lst [1, 2, 3]]) ] }

def pCaseNested : Program := {
  name := "CaseNestedTest",
  defs := [ .fn "describe" [pv "a", pv "b"] (caseOf (v "a") [
    (pcon "Just" [pw], caseOf (v "b") [(pcon "Just" [pw], str "both"), (pcon "Nothing" [], str "first")]),
    (pcon "Nothing" [], caseOf (v "b") [(pcon "Just" [pw], str "second"), (pcon "Nothing" [], str "neither")]) ]) ],
  checks := [
    ck "nested1" "\"both\"" (ap (v "describe") [ap (c "Just") [i 1], ap (c "Just") [i 2]]),
    ck "nested2" "\"first\"" (ap (v "describe") [ap (c "Just") [i 1], c "Nothing"]),
    ck "nested3" "\"second\"" (ap (v "describe") [c "Nothing", ap (c "Just") [i 2]]),
    ck "nested4" "\"neither\"" (ap (v "describe") [c "Nothing", c "Nothing"]) ] }

def pCaseTuple : Program := {
  name := "CaseTupleTest",
  defs := [ .fn "describePair" [pv "pair"] (caseOf (v "pair") [
    (P (ptup2 (P (pint 0)) (P (pint 0))), str "both zero"),
    (P (ptup2 (P (pint 0)) (P pw)), str "x is zero"),
    (P (ptup2 (P pw) (P (pint 0))), str "y is zero"),
    (P pw, str "neither zero") ]) ],
  checks := [
    ck "pair1" "\"both zero\"" (ap (v "describePair") [tup2 (i 0) (i 0)]),
    ck "pair2" "\"x is zero\"" (ap (v "describePair") [tup2 (i 0) (i 5)]),
    ck "pair3" "\"y is zero\"" (ap (v "describePair") [tup2 (i 3) (i 0)]),
    ck "pair4" "\"neither zero\"" (ap (v "describePair") [tup2 (i 1) (i 2)]) ] }

def pCaseTree : Program := {
  name := "CaseTreeTest",
  cons := [("Leaf", 0), ("Node", 3)],
  defs := [ .fn "countNodes" [pv "tree"] (caseOf (v "tree") [
    (pcon "Leaf" [], i 0),
    (pcon "Node" [pv "left", pw, pv "right"],
      bin "+" (bin "+" (i 1) (ap (v "countNodes") [v "left"])) (ap (v "countNodes") [v "right"])) ]) ],
  checks := [
    ck "tree1" "0" (ap (v "countNodes") [c "Leaf"]),
    ck "tree2" "1" (ap (v "countNodes") [ap (c "Node") [c "Leaf", i 1, c "Leaf"]]),
    ck "tree3" "3" (ap (v "countNodes") [ap (c "Node")
      [ap (c "Node") [c "Leaf", i 2, c "Leaf"], i 1, ap (c "Node") [c "Leaf", i 3, c "Leaf"]]]) ] }

def pCaseChar : Program := {
  name := "CaseCharTest",
  defs := [ .fn "describeChar" [pv "c"] (caseOf (v "c") [
    (P (pchar 'a'), str "vowel a"), (P (pchar 'e'), str "vowel e"),
    (P (pchar 'i'), str "vowel i"), (P (pchar 'o'), str "vowel o"),
    (P (pchar 'u'), str "vowel u"), (P pw, str "other") ]) ],
  checks := [
    ck "char1" "\"vowel a\"" (ap (v "describeChar") [chA 'a']),
    ck "char2" "\"vowel e\"" (ap (v "describeChar") [chA 'e']),
    ck "char3" "\"other\"" (ap (v "describeChar") [chA 'x']),
    ck "char4" "\"other\"" (ap (v "describeChar") [chA 'z']) ] }

def pLetDestructuring : Program := {
  name := "LetDestructuringTest",
  locals := [
    .pat (ptup2 (P (pv "first")) (P (pv "second"))) (tup2 (i 1) (i 2)),
    .pat (ptup3 (P (pv "a")) (P (pv "b")) (P (pv "c"))) (tup3 (i 10) (i 20) (i 30)) ],
  checks := [
    ck "first" "1" (v "first"), ck "second" "2" (v "second"), ck "head" "10" (v "a") ] }

def pLetDestructRecord : Program := {
  name := "LetDestructRecordTest",
  locals := [
    .pat (precord ["x"]) (recE [("x", i 42)]),
    .pat (precord ["a", "b"]) (recE [("a", i 1), ("b", i 2)]),
    .pat (precord ["p", "r"]) (recE [("p", i 1), ("q", i 2), ("r", i 3)]),
    .pat (ptup2 (P (precord ["s"])) (P (pv "t"))) (tup2 (recE [("s", i 1)]) (i 2)) ],
  checks := [
    ck "single" "42" (v "x"),
    ck "multi" "3" (bin "+" (v "a") (v "b")),
    ck "partial" "4" (bin "+" (v "p") (v "r")),
    ck "mixed" "3" (bin "+" (v "s") (v "t")) ] }

def pLetRecMultiArg : Program := {
  name := "LetRecMultiArgTest",
  locals := [
    .fn "f" [pv "a", pv "b"] (ifte (bin "<=" (v "a") (i 0)) (v "b")
      (ap (v "f") [bin "-" (v "a") (i 1), bin "+" (v "b") (i 1)])),
    .fn "result" [] (ap (v "f") [i 1, i 1]) ],
  checks := [ ck "result" "2" (v "result") ] }

def pLetRecClosure : Program := {
  name := "LetRecClosureTest",
  cons := [("Num", 1), ("Blank", 0)],
  defs := [ .fn "processItems" [pv "threshold", pv "items"] (caseOf (v "items") [
    (P .nil, .atexp .nil),
    (.cons (P (PA (pcon "Num" [pv "n"]))) (P (pv "rest")),
      letDefs [
        .fn "collected" [] (ap (v "takeMore") [v "rest"]),
        .fn "takeMore" [pv "xs"] (caseOf (v "xs") [
          (.cons (P (PA (pcon "Num" [pv "m"]))) (P (pv "ys")),
            ifte (bin ">" (v "m") (v "threshold"))
              (bin "::" (v "m") (ap (v "takeMore") [v "ys"])) (.atexp .nil)),
          (P pw, .atexp .nil) ]) ]
        (bin "::" (v "n") (v "collected"))),
    (.cons (pcon "Blank" []) (P (pv "rest")), ap (v "processItems") [v "threshold", v "rest"]) ]) ],
  locals := [
    .fn "items" [] (listE [ap (c "Num") [i 1], ap (c "Num") [i 2], ap (c "Num") [i 3], c "Blank",
                           ap (c "Num") [i 99]]),
    .fn "result" [] (ap (v "processItems") [i 0, v "items"]) ],
  checks := [ ck "LetRecClosureTest" "[1,2,3]" (v "result") ] }

def pRecordUpdate : Program := {
  name := "RecordUpdateTest",
  locals := [
    .fn "original" [] (recE [("x", i 1), ("y", i 2)]),
    .fn "updated" [] (updE "original" [("x", i 10)]) ],
  checks := [
    ck "updated" "{ x = 10, y = 2 }" (v "updated"),
    ck "original" "{ x = 1, y = 2 }" (v "original") ] }

def pRecordChainedUpdate : Program := {
  name := "RecordChainedUpdateTest",
  locals := [
    .fn "r" [] (recE [("x", i 1), ("y", i 20), ("z", i 3)]),
    .fn "multi" [] (updE "r" [("x", i 100), ("z", i 300)]),
    .fn "s" [] (recE [("x", i 1), ("y", i 2)]),
    .fn "s2" [] (updE "s" [("x", i 10)]),
    .fn "chain" [] (updE "s2" [("y", i 20)]) ],
  checks := [
    ck "multi" "{ x = 100, y = 20, z = 300 }" (v "multi"),
    ck "chain" "{ x = 10, y = 20 }" (v "chain") ] }

def pRecordAccess : Program := {
  name := "RecordAccessTest",
  locals := [
    .fn "point" [] (recE [("x", i 1), ("y", i 2)]),
    .fn "person" [] (recE [("name", str "Alice"), ("age", i 30)]) ],
  checks := [
    ck "x" "1" (.atexp (access (vA "point") "x")),
    ck "y" "2" (.atexp (access (vA "point") "y")),
    ck "name" "\"Alice\"" (.atexp (access (vA "person") "name")) ] }

def pClosureCapture01 : Program := {
  name := "ClosureCapture01Test",
  cons := [("Wrap", 1)],
  defs := [ .fn "unwrapLater" [pv "w"]
    (lams [pv "dummy"] (caseOf (v "w") [(pcon "Wrap" [pv "x"], v "x")])) ],
  checks := [
    ck "unwrap1" "42" (ap (v "unwrapLater") [ap (c "Wrap") [i 42], i 0]),
    ck "unwrap2" "99" (ap (v "unwrapLater") [ap (c "Wrap") [i 99], i 0]) ] }

def pRecursiveFactorial : Program := {
  name := "RecursiveFactorialTest",
  defs := [ .fn "factorial" [pv "n"] (ifte (bin "<=" (v "n") (i 1)) (i 1)
    (bin "*" (v "n") (ap (v "factorial") [bin "-" (v "n") (i 1)]))) ],
  checks := [
    ck "fact0" "1" (ap (v "factorial") [i 0]),
    ck "fact5" "120" (ap (v "factorial") [i 5]),
    ck "fact10" "3628800" (ap (v "factorial") [i 10]) ] }

def pRecursiveFibonacci : Program := {
  name := "RecursiveFibonacciTest",
  defs := [ .fn "fib" [pv "n"] (ifte (bin "<=" (v "n") (i 0)) (i 0)
    (ifte (eq (v "n") (i 1)) (i 1)
      (bin "+" (ap (v "fib") [bin "-" (v "n") (i 1)]) (ap (v "fib") [bin "-" (v "n") (i 2)])))) ],
  checks := [
    ck "fib0" "0" (ap (v "fib") [i 0]),
    ck "fib1" "1" (ap (v "fib") [i 1]),
    ck "fib10" "55" (ap (v "fib") [i 10]) ] }

def pMutualRecursion : Program := {
  name := "MutualRecursionTest",
  defs := [
    .fn "isEven" [pv "n"] (ifte (eq (v "n") (i 0)) T (ap (v "isOdd") [bin "-" (v "n") (i 1)])),
    .fn "isOdd" [pv "n"] (ifte (eq (v "n") (i 0)) F (ap (v "isEven") [bin "-" (v "n") (i 1)])) ],
  checks := [
    ck "isEven0" "True" (ap (v "isEven") [i 0]),
    ck "isEven5" "False" (ap (v "isEven") [i 5]),
    ck "isOdd5" "True" (ap (v "isOdd") [i 5]) ] }

def pTailRecursiveSum : Program := {
  name := "TailRecursiveSumTest",
  defs := [
    .fn "sumHelper" [pv "n", pv "acc"] (ifte (bin "<=" (v "n") (i 0)) (v "acc")
      (ap (v "sumHelper") [bin "-" (v "n") (i 1), bin "+" (v "acc") (v "n")])),
    .fn "sumTo" [pv "n"] (ap (v "sumHelper") [v "n", i 0]) ],
  checks := [
    ck "sum1" "15" (ap (v "sumTo") [i 5]),
    ck "sum2" "55" (ap (v "sumTo") [i 10]),
    ck "sum3" "5050" (ap (v "sumTo") [i 100]) ] }

def pPartialAppChain : Program := {
  name := "PartialAppChainTest",
  defs := [ .fn "addThree" [pv "a", pv "b", pv "c"] (bin "+" (bin "+" (v "a") (v "b")) (v "c")) ],
  locals := [
    .fn "addTo3" [] (ap (v "addThree") [i 3]),
    .fn "addTo3And4" [] (ap (v "addTo3") [i 4]) ],
  checks := [
    ck "chain1" "10" (ap (v "addTo3And4") [i 3]),
    ck "chain2" "6" (ap (v "addThree") [i 1, i 2, i 3]) ] }

def pIntSub : Program := {
  name := "IntSubTest", source := "tests/elm-core/src", checks := [
  ck "sub1" "7" (bin "-" (i 10) (i 3)),
  ck "sub2" "10" (bin "-" (i 5) (i (-5))),
  ck "sub3" "1" (bin "-" (i (-2)) (i (-3))) ] }

def pCompareInt : Program := {
  name := "CompareIntTest", source := "tests/elm-core/src", checks := [
  ck "cmp1" "LT" (ap (v "compare") [i 1, i 2]),
  ck "cmp2" "GT" (ap (v "compare") [i 3, i 2]),
  ck "cmp3" "EQ" (ap (v "compare") [i 5, i 5]) ] }

def pCaseMaybe : Program := {
  name := "CaseMaybeTest",
  defs := [ .fn "maybeToInt" [pv "maybe"] (caseOf (v "maybe") [
    (pcon "Just" [pv "x"], v "x"), (pcon "Nothing" [], i (-1)) ]) ],
  checks := [
    ck "case1" "42" (ap (v "maybeToInt") [ap (c "Just") [i 42]]),
    ck "case2" "-1" (ap (v "maybeToInt") [c "Nothing"]) ] }

def pCaseInt : Program := {
  name := "CaseIntTest",
  defs := [ .fn "describeNum" [pv "n"] (caseOf (v "n") [
    (P (pint 1), str "one"), (P (pint 2), str "two"), (P pw, str "other") ]) ],
  checks := [
    ck "case1" "\"one\"" (ap (v "describeNum") [i 1]),
    ck "case2" "\"two\"" (ap (v "describeNum") [i 2]),
    ck "case3" "\"other\"" (ap (v "describeNum") [i 99]) ] }

/-- The 40 corpus programs. -/
def corpus : List Program :=
  [ pIntAdd, pIntSub, pIntMul, pIntDiv, pIntDivByZero, pIntModBy, pIntRemainderBy, pIntPow,
    pIntNegate, pIntAbs, pIntCompare, pIntMinMax,
    pBoolAnd, pBoolOr, pBoolNot, pBoolXor, pBoolShortCircuit,
    pCompareInt, pCompareChar, pCompareEmptyList, pCompareTupleWithEmptyList,
    pEquality, pEqualityBoolContainer, pEqualityBoolRecord,
    pCaseCustomType, pCaseListCons, pCaseNested, pCaseTuple, pCaseTree, pCaseChar, pCaseMaybe,
    pCaseInt,
    pLetDestructuring, pLetDestructRecord, pLetRecMultiArg, pLetRecClosure,
    pRecordUpdate, pRecordChainedUpdate, pRecordAccess,
    pClosureCapture01, pRecursiveFactorial, pRecursiveFibonacci, pMutualRecursion,
    pTailRecursiveSum, pPartialAppChain ].filter (fun p => !(dropped.contains p.name))
where
  /-- Five candidates written above but left out to keep the corpus at 40. -/
  dropped : List String := ["IntSubTest", "CompareIntTest", "CaseMaybeTest", "CaseIntTest",
                            "RecursiveFibonacciTest"]

/-! ## Rulings: A40, A42, A43 and A51 -/

/-- tests/elm-core/src/StandardA42ZeroDivisorTest (A42): the book's examples. -/
def pA42ZeroDivisor : Program := {
  name := "StandardA42ZeroDivisorTest", source := "tests/elm-core/src",
  checks := [
    ck "3 // 0" "0" (bin "//" (i 3) (i 0)),
    ck "modBy 0 3" "0" (ap (v "modBy") [i 0, i 3]),
    ck "remainderBy 0 3" "0" (ap (v "remainderBy") [i 0, i 3]) ] }

/-- tests/elm-core/src/StandardA42ModByZeroTest (A42). -/
def pA42ModByZero : Program := {
  name := "StandardA42ModByZeroTest", source := "tests/elm-core/src",
  checks := [
    ck "modBy 0 7 + 1 == 1" "True" (eq (bin "+" (ap (v "modBy") [i 0, i 7]) (i 1)) (i 1)),
    ck "modBy 0 -7 + 1 == 1" "True" (eq (bin "+" (ap (v "modBy") [i 0, i (-7)]) (i 1)) (i 1)) ] }

/-- tests/elm-core/src/StandardA42RemainderByZeroTest (A42). -/
def pA42RemainderByZero : Program := {
  name := "StandardA42RemainderByZeroTest", source := "tests/elm-core/src",
  checks := [
    ck "remainderBy 0 7 + 1 == 1" "True" (eq (bin "+" (ap (v "remainderBy") [i 0, i 7]) (i 1)) (i 1)),
    ck "remainderBy 0 7" "0" (ap (v "remainderBy") [i 0, i 7]) ] }

/-- tests/elm-core/src/StandardA43PowNegativeTest (A43): Int `^` with a
    negative exponent, with the book's values. -/
def pA43PowNegative : Program := {
  name := "StandardA43PowNegativeTest", source := "tests/elm-core/src",
  checks := [
    ck "1 ^ -1" "1" (bin "^" (i 1) (i (-1))),
    ck "(-1) ^ -3" "-1" (bin "^" (.atexp (.paren (i (-1)))) (i (-3))),
    ck "(-1) ^ -2" "1" (bin "^" (.atexp (.paren (i (-1)))) (i (-2))),
    ck "2 ^ -1 + 1 == 1" "True" (eq (bin "+" (bin "^" (i 2) (i (-1))) (i 1)) (i 1)),
    ck "0 ^ -1 + 1 == 1" "True" (eq (bin "+" (bin "^" (i 0) (i (-1))) (i 1)) (i 1)) ] }

/-- tests/elm-core/src/StandardA51FunctionEqualityTest (A51): comparing two
    functions gives a Boolean, either one. -/
def pA51FunctionEquality : Program := {
  name := "StandardA51FunctionEqualityTest", source := "tests/elm-core/src",
  locals := [
    .fn "same" [] (eq (.atexp (.paren (lams [pv "k"] (bin "+" (v "k") (i 1)))))
                      (.atexp (.paren (lams [pv "k"] (bin "+" (v "k") (i 2)))))) ],
  checks := [
    ck "compared" "True" (orelse (v "same") (ap (v "not") [v "same"])) ] }

/-- tests/elm-core/src/StandardA40IntOverflowTest (A40): with the Int range
    of this encoding (64-bit, wrapping), as with any range the book allows. -/
def pA40IntOverflow : Program := {
  name := "StandardA40IntOverflowTest", source := "tests/elm-core/src",
  defs := [
    .fn "big" [] (bin "^" (i 10) (i 200)),
    .fn "huge" [] (bin "^" (i 10) (i 308)) ],
  checks := [
    ck "big * big - big * big + 1 == 1" "True"
      (eq (bin "+" (bin "-" (bin "*" (v "big") (v "big")) (bin "*" (v "big") (v "big"))) (i 1)) (i 1)),
    ck "huge + huge - (huge + huge) + 1 == 1" "True"
      (eq (bin "+" (bin "-" (bin "+" (v "huge") (v "huge"))
                            (.atexp (.paren (bin "+" (v "huge") (v "huge"))))) (i 1)) (i 1)) ] }

/-! ## Floats: equality and order (A46, A47, A48, A49, A50) -/

/-- An integer constant at Float, after number specialisation. -/
def fI (n : Nat) : Exp := .atexp (.scon (.intF n))

/-- The float constant 0.5. -/
def fHalf : Exp := .atexp (.scon (.float 5 (-1)))


/-- tests/elm-core/src/StandardA46CompareNanTest (A46): compare with NaN. -/
def pA46CompareNan : Program := {
  name := "StandardA46CompareNanTest", source := "tests/elm-core/src",
  defs := [ .fn "nan" [] (bin "/" (fI 0) (fI 0)) ],
  checks := [
    ck "compare 1 nan" "LT" (ap (v "compare") [fI 1, v "nan"]),
    ck "compare nan nan" "EQ" (ap (v "compare") [v "nan", v "nan"]),
    ck "compare nan 1" "GT" (ap (v "compare") [v "nan", fI 1]) ] }

/-- tests/elm-core/src/StandardA48MinMaxNanTest (A48), the checks on signed
    zeros. Its checks on NaN use isNaN, which is outside the part of APPLY
    this encoding covers. -/
def pA48MinMaxNan : Program := {
  name := "StandardA48MinMaxNanTest", source := "tests/elm-core/src",
  defs := [
    .fn "nan" [] (bin "/" (fI 0) (fI 0)),
    .fn "zero" [] (fI 0),
    .fn "negativeZero" [] (.atexp (neg (vA "zero"))) ],
  checks := [
    ck "min 0 -0 is -0" "True" (bin "<" (bin "/" (fI 1) (ap (v "min") [v "zero", v "negativeZero"])) (fI 0)),
    ck "min -0 0 is -0" "True" (bin "<" (bin "/" (fI 1) (ap (v "min") [v "negativeZero", v "zero"])) (fI 0)),
    ck "max 0 -0 is +0" "True" (bin ">" (bin "/" (fI 1) (ap (v "max") [v "zero", v "negativeZero"])) (fI 0)),
    ck "max -0 0 is +0" "True" (bin ">" (bin "/" (fI 1) (ap (v "max") [v "negativeZero", v "zero"])) (fI 0)) ] }

/-- tests/elm-core/src/CoreIssue1080ClampNanTest (A49): `clamp -100 100 (0 / 0)`. -/
def pClampNan : Program := {
  name := "CoreIssue1080ClampNanTest",
  source := "tests/elm-core/src",
  checks := [
    ck "clamp nan" "NaN" (ap (v "clamp") [.atexp (neg (.scon (.intF 100))), fI 100,
      .atexp (.paren (bin "/" (fI 0) (fI 0)))]) ] }

/-- tests/elm-core/src/StandardA49ClampTest (A49): the book's examples. At
    Float, clamp lo hi x is min (max x lo) hi with IEEE minimum and maximum;
    at Int, the elm/core text. -/
def pA49Clamp : Program := {
  name := "StandardA49ClampTest", source := "tests/elm-core/src",
  defs := [
    .fn "nan" [] (bin "/" (fI 0) (fI 0)),
    .fn "negZero" [] (.atexp (neg (.scon (.intF 0)))),
    .fn "isNotSelf" [pv "x"] (bin "/=" (v "x") (v "x")),
    .fn "isPositiveZero" [pv "x"] (andalso (eq (v "x") (fI 0)) (bin ">" (bin "/" (fI 1) (v "x")) (fI 0))),
    .fn "isNegativeZero" [pv "x"] (andalso (eq (v "x") (fI 0)) (bin "<" (bin "/" (fI 1) (v "x")) (fI 0))) ],
  checks := [
    ck "clamp 10 0 5 at Float is +0" "True" (ap (v "isPositiveZero") [ap (v "clamp") [fI 10, fI 0, fI 5]]),
    ck "clamp nan 1 0.5 is NaN" "True" (ap (v "isNotSelf") [ap (v "clamp") [v "nan", fI 1, fHalf]]),
    ck "clamp 0 1 -0 is +0" "True" (ap (v "isPositiveZero") [ap (v "clamp") [fI 0, fI 1, v "negZero"]]),
    ck "clamp -1 -0 0 is -0" "True"
      (ap (v "isNegativeZero") [ap (v "clamp") [.atexp (neg (.scon (.intF 1))), v "negZero", fI 0]]),
    ck "clamp 10 0 5 at Int" "10" (ap (v "clamp") [i 10, i 0, i 5]),
    ck "clamp 10 0 20 at Int" "0" (ap (v "clamp") [i 10, i 0, i 20]),
    ck "clamp 0 10 -5 at Int" "0" (ap (v "clamp") [i 0, i 10, i (-5)]),
    ck "clamp 0 10 15 at Int" "10" (ap (v "clamp") [i 0, i 10, i 15]),
    ck "clamp 0 10 7 at Int" "7" (ap (v "clamp") [i 0, i 10, i 7]) ] }

/-- tests/elm-core/src/CompilerIssue2362NanTupleEqualityTest (A50). -/
def pNanTuple : Program := {
  name := "CompilerIssue2362NanTupleEqualityTest",
  source := "tests/elm-core/src",
  locals := [
    .fn "nan" [] (bin "/" (fI 0) (fI 0)),
    .fn "p" [] (tup2 (v "nan") (fI 1)),
    .fn "q" [] (tup2 (bin "/" (fI 0) (fI 0)) (fI 1)) ],
  checks := [
    ck "nan == nan" "False" (eq (v "nan") (v "nan")),
    ck "p == q" "False" (eq (v "p") (v "q")),
    ck "p == p" "False" (eq (v "p") (v "p")) ] }

/-- tests/elm/src/CoreIssue988NanContainerSelfEqualityTest (A50), the checks
    that use no Array, Dict or Set. -/
def pNanContainer : Program := {
  name := "CoreIssue988NanContainerSelfEqualityTest",
  source := "tests/elm/src",
  cons := [("Box", 1)],
  locals := [
    .fn "nan" [] (bin "/" (fI 0) (fI 0)),
    .fn "record" [] (recE [("x", v "nan")]),
    .fn "box" [] (ap (c "Box") [v "nan"]),
    .fn "maybe" [] (ap (c "Just") [v "nan"]),
    .fn "inner" [] (tup2 (v "nan") (fI 1)) ],
  checks := [
    ck "record" "False" (eq (v "record") (v "record")),
    ck "custom type" "False" (eq (v "box") (v "box")),
    ck "maybe" "False" (eq (v "maybe") (v "maybe")),
    ck "shared inner tuple" "False" (eq (tup2 (v "inner") (i 2)) (tup2 (v "inner") (i 2))),
    ck "shared inner list" "False" (eq (listE [v "inner"]) (listE [v "inner"])) ] }

/-- The examples of the rulings: every one a test program of tests/. -/
def rulings : List Program :=
  [pA42ZeroDivisor, pA42ModByZero, pA42RemainderByZero, pA43PowNegative, pA51FunctionEquality,
   pA40IntOverflow, pA46CompareNan, pA48MinMaxNan, pClampNan, pA49Clamp, pNanTuple, pNanContainer]

/-! ## Rule coverage: tests for rules the corpus reaches only in passing, and
    examples from the book's Comments -/

/-- tests/elm/src/StandardCoreEvaluationExamplesTest. -/
def pCoreEvaluationExamples : Program := {
  name := "StandardCoreEvaluationExamplesTest", source := "tests/elm/src",
  cons := [("Leaf", 0), ("Node", 3)],
  defs := [ .fn "add1" [pv "n"] (bin "+" (v "n") (i 1)) ],
  checks := [
    -- r:d-pat-as, r:d-pat-cons with a wildcard
    ck "as-pattern" "(1,[1,2])" (caseOf (lst [1, 2])
      [(.as (.cons (P (pv "x")) (P pw)) "whole", tup2 (v "x") (v "whole")),
       (P pw, tup2 (i 0) (.atexp .nil))]),
    -- r:d-atpat-unit, r:d-atexp-unit
    ck "unit pattern" "5" (ap (.atexp (.paren (lams [.unit] (i 5)))) [.atexp .unit]),
    -- r:d-atexp-op as a value, r:d-app-basic-partial
    ck "operator value" "3" (ap (.atexp (.op "+")) [i 1, i 2]),
    ck "partial basic value" "<function>" (ap (.atexp (.op "+")) [i 1]),
    -- r:d-app-con with a constructor awaiting arguments
    ck "partial constructor" "<function>" (ap (c "Node") [c "Leaf"]),
    -- Comment on r:d-atexp-op: (&&) receives both arguments as values
    ck "(&&) is strict" "False" (ap (.atexp (.op "&&")) [F, T]),
    -- |> (a text of fig:dynamic-basis-elm)
    ck "pipe" "6" (bin "|>" (i 5) (v "add1")),
    -- Comment on r:d-mrule-fail: a failing rule's body is not evaluated
    ck "mrule-fail" "2" (caseOf (i 1)
      [(P (pint 0), ap (qv "Debug" "todo") [str "x"]), (P pw, i 2)]),
    -- Comment on r:d-app-con: Just applied to 1
    ck "Just 1" "Just 1" (ap (c "Just") [i 1]),
    -- r:d-atexp-scon at Float after specialisation (A87): incF 0.5 = 1.5 with 1 : Float
    ck "inc 0.5" "1.5" (letDefs [.fn "incF" [pv "n"] (bin "+" (v "n") (.atexp (.scon (.intF 1))))]
      (ap (v "incF") [.atexp (.scon (.float 5 (-1)))])),
    -- sec:appendix-dynamic-basis-intarith: modBy 4 -5 is 3, remainderBy 4 -5 is -1
    ck "modBy 4 -5" "3" (ap (v "modBy") [i 4, i (-5)]),
    ck "remainderBy 4 -5" "-1" (ap (v "remainderBy") [i 4, i (-5)]),
    -- records are finite maps: the order in which fields are written is immaterial
    ck "record field order" "True" (eq (recE [("a", i 1), ("b", i 2)]) (recE [("b", i 2), ("a", i 1)])),
    -- order of comparable strings (cmp clause 4)
    ck "compare strings" "LT" (ap (v "compare") [str "ab", str "abc"]),
    -- the field accessor .k (derived form) through r:d-atpat-record and r:d-patrow-field
    ck "accessor" "7" (ap (.atexp (accessor "k")) [recE [("k", i 7), ("j", i 8)]]) ] }

/-- tests/elm/src/StandardLetStrictTest: the Comment on r:d-atexp-let,
    `let _ = Debug.todo "x" in 1` has no value. -/
def pLetStrict : Program := {
  name := "StandardLetStrictTest", source := "tests/elm/src",
  checks := [
    ck "before" "()" (.atexp .unit),
    ck "let strict" "(no value)" (letDefs [.pat pw (ap (qv "Debug" "todo") [str "x"])] (i 1)) ] }

/-- tests/elm/src/StandardApplicationStrictTest: the Comment on r:d-exp-app,
    `(\_ -> 1) (Debug.todo "x")` has no value. -/
def pAppStrict : Program := {
  name := "StandardApplicationStrictTest", source := "tests/elm/src",
  checks := [
    ck "before" "()" (.atexp .unit),
    ck "app strict" "(no value)"
      (ap (.atexp (.paren (lams [pw] (i 1)))) [ap (qv "Debug" "todo") [str "x"]]) ] }

def coverage : List Program := [pCoreEvaluationExamples, pLetStrict, pAppStrict]

end StandardElm
