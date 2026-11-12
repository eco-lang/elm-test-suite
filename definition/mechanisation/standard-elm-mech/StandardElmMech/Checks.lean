/-
  A Standard Definition of Elm? Mechanisation: what a check of a test states (plan decision D9).

  * `Expect`: the value a CHECK line states, structurally: Ints, floats as Elm prints them, numbers of
    either kind, characters, strings, (), constructor values with arguments, lists, tuples, records
    (the labels as a set), functions. `Expect.holds x v` is decided by `Expect.check`.
  * `CheckStmt`: what a CHECK line states of a value: one the line describes, or none.
  * The log statements (`EntryPat`, `LogCheck`, `ExpChecks`): what a check says of the log of a
    logged derivation (step 3 of the plan states every check of a test program this way; the let
    form of steps 1 and 2, one phrase per check, is retired).

  Each statement has a Boolean decider proved sound, so that a theorem is `decide +kernel` (or
  `native_decide`) on the decider.
-/
import StandardElmMech.Examples
import StandardElmMech.Determinism

namespace StandardElm

/-! ## The value a CHECK line states -/

inductive Expect where
  | int (n : Int)
  /-- a Float, as `showFloat` prints it -/
  | flt (s : String)
  /-- a number of either kind whose printed form is `s` (inside data the translator gives no type) -/
  | num (s : String)
  | chr (c : Char)
  | str (s : String)
  | unit
  /-- a complete constructor value, other than `[]` and `::` -/
  | con (name : String) (args : List Expect)
  | list (es : List Expect)
  /-- two or three components -/
  | tuple (es : List Expect)
  /-- the labels as a set -/
  | record (fs : List (String × Expect))
  /-- a function value (`<function>`) -/
  | fn
  deriving Inhabited, Repr

mutual
  def Expect.check : Expect → Val → Bool
    | .int n, .sv (.int m) => m == n
    | .flt s, .sv (.float x) => showFloat x == s
    | .num s, .sv (.int m) => toString m == s
    | .num s, .sv (.float x) => showFloat x == s
    | .chr c, .sv (.char c') => c' == c
    | .str s, .sv (.str s') => s' == s
    | .unit, .unit => true
    | .con k xs, .con c vs =>
      c.name == k && c != conNil && c != conCons && vs.length == c.arity && Expect.checkList xs vs
    | .list xs, v =>
      match v.toList? with
      | some vs => Expect.checkList xs vs
      | none => false
    | .tuple [a, b], .tuple v1 v2 none => a.check v1 && b.check v2
    | .tuple [a, b, c], .tuple v1 v2 (some v3) => a.check v1 && b.check v2 && c.check v3
    | .record fs, .record r =>
      (fmDom r).all (fun l => fs.any (·.1 == l)) && fs.length == (fmDom r).length &&
        Expect.checkFields fs r
    | .fn, v => isFun v
    | _, _ => false
  def Expect.checkList : List Expect → List Val → Bool
    | [], [] => true
    | x :: xs, v :: vs => x.check v && Expect.checkList xs vs
    | _, _ => false
  def Expect.checkFields : List (String × Expect) → Record → Bool
    | [], _ => true
    | (l, x) :: fs, r =>
      match fmLookup r l with
      | some v => x.check v && Expect.checkFields fs r
      | none => false
end

/-- `x.holds v`: v is a value the CHECK line describes. -/
def Expect.holds (x : Expect) (v : Val) : Prop := x.check v = true

theorem Expect.holds_int {n : Int} {v : Val} : (Expect.int n).holds v ↔ v = .sv (.int n) := by
  unfold Expect.holds; cases v <;> simp [Expect.check] <;> (try rename_i s; cases s) <;>
    simp [Expect.check] <;> exact eq_comm

theorem Expect.holds_str {s : String} {v : Val} : (Expect.str s).holds v ↔ v = .sv (.str s) := by
  unfold Expect.holds; cases v <;> simp [Expect.check] <;> (try rename_i t; cases t) <;>
    simp [Expect.check] <;> exact eq_comm

/-! ## Parsing a CHECK line's printed value (generation only) -/

/-- The shape of a value, from the translator's kind of a check. -/
inductive Shape where
  | any | int | float | char | string | fn
  deriving Inhabited, BEq

namespace ExpectParse

/-- Reads Elm's printed form of a value, as `showElm` prints it, into an `Expect`. Used only when
    generating theorem statements, which then show the result literally; not trusted. -/
partial def value (cs : List Char) : Option (Expect × List Char) :=
  let cs := cs.dropWhile (· == ' ')
  match cs with
  | '(' :: ')' :: rest => some (.unit, rest)
  | '(' :: rest =>
    match items ')' rest with
    | some (es, rest') =>
      match es with
      | [e] => some (e, rest')
      | _ => some (.tuple es, rest')
    | none => none
  | '[' :: rest =>
    match items ']' rest with
    | some (es, rest') => some (.list es, rest')
    | none => none
  | '{' :: rest => record rest
  | '"' :: rest => str rest []
  | '\'' :: c :: '\'' :: rest => some (.chr c, rest)
  | '<' :: rest =>
    let (w, rest') := rest.span (· != '>')
    if String.ofList w == "function" then some (.fn, rest'.drop 1) else none
  | c :: _ =>
    if c.isUpper then
      let (w, rest) := cs.span (fun c => c.isAlphanum || c == '_')
      args (String.ofList w) [] rest
    else
      let (w, rest) := cs.span (fun c => c.isAlphanum || c == '.' || c == '-' || c == '+')
      if w.isEmpty then none else some (.num (String.ofList w), rest)
  | [] => none
where
  items (close : Char) (cs : List Char) : Option (List Expect × List Char) :=
    match cs.dropWhile (· == ' ') with
    | c :: rest => if c == close then some ([], rest) else itemsAux close cs []
    | [] => none
  itemsAux (close : Char) (cs : List Char) (acc : List Expect) : Option (List Expect × List Char) :=
    match value cs with
    | some (e, rest) =>
      match rest.dropWhile (· == ' ') with
      | ',' :: rest' => itemsAux close rest' (acc ++ [e])
      | c :: rest' => if c == close then some (acc ++ [e], rest') else none
      | [] => none
    | none => none
  str (cs : List Char) (acc : List Char) : Option (Expect × List Char) :=
    match cs with
    | '\\' :: c :: rest => str rest (acc ++ [unescape c])
    | '"' :: rest => some (.str (String.ofList acc), rest)
    | c :: rest => str rest (acc ++ [c])
    | [] => none
  -- the escapes of Elm/JS's Debug.toString (`_Debug_addSlashes`)
  unescape : Char → Char
    | 'n' => '\n'
    | 't' => '\t'
    | 'r' => '\r'
    | 'v' => '\x0b'
    | '0' => '\x00'
    | c => c
  record (cs : List Char) : Option (Expect × List Char) :=
    match cs.dropWhile (· == ' ') with
    | '}' :: rest => some (.record [], rest)
    | cs' => fields cs' []
  fields (cs : List Char) (acc : List (String × Expect)) : Option (Expect × List Char) :=
    let cs := cs.dropWhile (· == ' ')
    let (l, rest) := cs.span (fun c => c.isAlphanum || c == '_')
    match (rest.dropWhile (· == ' ')) with
    | '=' :: rest' =>
      match value rest' with
      | some (e, rest'') =>
        match rest''.dropWhile (· == ' ') with
        | ',' :: r => fields r (acc ++ [(String.ofList l, e)])
        | '}' :: r => some (.record (acc ++ [(String.ofList l, e)]), r)
        | _ => none
      | none => none
    | _ => none
  /-- The arguments of a constructor: atomic values or parenthesised ones, up to `,`, `)`, `]`,
      `}` or the end. -/
  args (name : String) (acc : List Expect) (cs : List Char) : Option (Expect × List Char) :=
    match cs with
    | ' ' :: rest =>
      match rest with
      | c :: _ =>
        if c == ',' || c == ')' || c == ']' || c == '}' then some (.con name acc, cs)
        else if c.isUpper then
          -- an argument printed without parentheses is atomic: a constructor with no arguments
          let (w, rest') := rest.span (fun c => c.isAlphanum || c == '_')
          args name (acc ++ [.con (String.ofList w) []]) rest'
        else
          match value rest with
          | some (e, rest') => args name (acc ++ [e]) rest'
          | none => none
      | [] => some (.con name acc, cs)
    | _ => some (.con name acc, cs)

end ExpectParse

/-- The `Expect` of a CHECK line's value text, at a shape. -/
def Expect.parse (s : Shape) (text : String) : Option Expect :=
  match s with
  | .int => text.toInt?.map .int
  | .float => some (.flt text)
  | _ =>
    match ExpectParse.value text.toList with
    | some (e, rest) => if rest.all (· == ' ') then some e else none
    | none => none

/-! ## What a CHECK line states of a value -/

inductive CheckStmt where
  | value (x : Expect)
  | noValue
  deriving Inhabited, Repr

def fuelT : Nat := 100000

/-! ## The log statements -/

/-- One CHECK pattern about one log entry. -/
inductive EntryPat where
  /-- `CHECK: label: value` -/
  | entry (label : String) (x : Expect)
  /-- a CHECK line with no `: `, which names an entry by its label -/
  | label (label : String)
  deriving Inhabited, Repr

def EntryPat.Holds : EntryPat → String × Val → Prop
  | .entry l x, (s, v) => s = l ∧ x.holds v
  | .label l, (s, _) => s = l

def EntryPat.check : EntryPat → String × Val → Bool
  | .entry l x, (s, v) => s == l && x.check v
  | .label l, (s, _) => s == l

theorem EntryPat.check_sound {p : EntryPat} {e : String × Val} : p.check e = true → p.Holds e := by
  cases p <;> obtain ⟨s, v⟩ := e <;> simp [EntryPat.check, EntryPat.Holds, Expect.holds]

/-- Regular expressions, the subset of JavaScript's that the suite's `{{...}}` patterns use. -/
inductive Rx where
  | eps
  | chr (c : Char)
  /-- `.`: any character but a newline -/
  | any
  /-- `[...]`, `[^...]`, `\d` -/
  | cls (neg : Bool) (ranges : List (Char × Char))
  /-- `^` and `$`: the ends of the input (no multiline flag) -/
  | bol | eol
  | seq (a b : Rx) | alt (a b : Rx) | star (a : Rx) | plus (a : Rx) | opt (a : Rx)
  deriving Inhabited, Repr

def Rx.inClass (ranges : List (Char × Char)) (c : Char) : Bool :=
  ranges.any fun (lo, hi) => lo.toNat ≤ c.toNat && c.toNat ≤ hi.toNat

/-- Backtracking matcher, with fuel: does `r` match a prefix of `s` (whose position in the input is
    `pos`) so that the continuation accepts the rest? -/
def Rx.m : Nat → Rx → Nat → List Char → (Nat → List Char → Bool) → Bool
  | 0, _, _, _, _ => false
  | _+1, .eps, pos, s, k => k pos s
  | _+1, .chr c, pos, s, k => match s with | c' :: s' => c' == c && k (pos + 1) s' | [] => false
  | _+1, .any, pos, s, k => match s with | c' :: s' => c' != '\n' && k (pos + 1) s' | [] => false
  | _+1, .cls neg rs, pos, s, k =>
    match s with | c' :: s' => (Rx.inClass rs c' != neg) && k (pos + 1) s' | [] => false
  | _+1, .bol, pos, s, k => pos == 0 && k pos s
  | _+1, .eol, pos, s, k => s.isEmpty && k pos s
  | n+1, .seq a b, pos, s, k => Rx.m n a pos s (fun p s' => Rx.m n b p s' k)
  | n+1, .alt a b, pos, s, k => Rx.m n a pos s k || Rx.m n b pos s k
  | n+1, .star a, pos, s, k =>
    Rx.m n a pos s (fun p s' => p != pos && Rx.m n (.star a) p s' k) || k pos s
  | n+1, .plus a, pos, s, k => Rx.m n a pos s (fun p s' => Rx.m n (.star a) p s' k)
  | n+1, .opt a, pos, s, k => Rx.m n a pos s k || k pos s

/-- JavaScript's `RegExp.test`: a match starting at some position. -/
def Rx.search (r : Rx) (s : String) : Bool :=
  let cs := s.toList
  let fuel := 64 * (cs.length + 8)
  (List.range (cs.length + 1)).any fun i => Rx.m fuel r i (cs.drop i) (fun _ _ => true)

/-- Parses the regular expressions of the suite's CHECK lines (generation only). -/
partial def Rx.parse (pattern : String) : Option Rx :=
  match alt pattern.toList with
  | some (r, []) => some r
  | _ => none
where
  alt (cs : List Char) : Option (Rx × List Char) := do
    let (a, rest) ← seqP cs
    match rest with
    | '|' :: rest' => let (b, rest'') ← alt rest'; pure (.alt a b, rest'')
    | _ => pure (a, rest)
  seqP (cs : List Char) : Option (Rx × List Char) :=
    match cs with
    | [] => some (.eps, [])
    | '|' :: _ => some (.eps, cs)
    | ')' :: _ => some (.eps, cs)
    | _ => do
      let (a, rest) ← postfixP cs
      let (b, rest') ← seqP rest
      pure (.seq a b, rest')
  postfixP (cs : List Char) : Option (Rx × List Char) := do
    let (a, rest) ← atom cs
    match rest with
    | '*' :: r => pure (.star a, r)
    | '+' :: r => pure (.plus a, r)
    | '?' :: r => pure (.opt a, r)
    | _ => pure (a, rest)
  atom (cs : List Char) : Option (Rx × List Char) :=
    match cs with
    | '(' :: '?' :: ':' :: rest => group rest
    | '(' :: rest => group rest
    | '.' :: rest => some (.any, rest)
    | '^' :: rest => some (.bol, rest)
    | '$' :: rest => some (.eol, rest)
    | '[' :: '^' :: rest => klass true rest []
    | '[' :: rest => klass false rest []
    | '\\' :: c :: rest => some (escape c, rest)
    | c :: rest => some (.chr c, rest)
    | [] => none
  group (cs : List Char) : Option (Rx × List Char) := do
    let (r, rest) ← alt cs
    match rest with
    | ')' :: rest' => pure (r, rest')
    | _ => none
  escape (c : Char) : Rx :=
    match c with
    | 'd' => .cls false [('0', '9')]
    | 's' => .cls false [(' ', ' '), ('\t', '\t'), ('\n', '\n'), ('\r', '\r')]
    | 'w' => .cls false [('a', 'z'), ('A', 'Z'), ('0', '9'), ('_', '_')]
    | 'n' => .chr '\n'
    | 't' => .chr '\t'
    | c => .chr c
  klass (neg : Bool) (cs : List Char) (acc : List (Char × Char)) : Option (Rx × List Char) :=
    match cs with
    | ']' :: rest => some (.cls neg acc, rest)
    | '\\' :: 'd' :: rest => klass neg rest (acc ++ [('0', '9')])
    | '\\' :: 'n' :: rest => klass neg rest (acc ++ [('\n', '\n')])
    | '\\' :: c :: rest => klass neg rest (acc ++ [(c, c)])
    | a :: '-' :: b :: rest => if b == ']' then klass neg (b :: rest) (acc ++ [(a, a), ('-', '-')])
      else klass neg rest (acc ++ [(a, b)])
    | a :: rest => klass neg rest (acc ++ [(a, a)])
    | [] => none

/-- The log printed as Elm/JS prints Debug.log lines (D9: used only for regex, unlabelled and
    CHECK-SAME lines, and CHECK-NOT patterns). -/
def renderLog (l : Log) : String := String.join (l.map fun (s, v) => s ++ ": " ++ showElm v ++ "\n")

/-- The patterns hold of the entries, one to one, in order. -/
def EntryPat.HoldsAll : List EntryPat → Log → Prop
  | [], [] => True
  | p :: ps, e :: l => p.Holds e ∧ EntryPat.HoldsAll ps l
  | _, _ => False

/-- The suffixes of a list, the list itself first. -/
def tailsOf {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: l => (a :: l) :: tailsOf l

theorem mem_tailsOf {α : Type} : ∀ {l t : List α}, t ∈ tailsOf l → ∃ pre, pre ++ t = l
  | [], t, h => by simp [tailsOf] at h; exact ⟨[], by simp [h]⟩
  | a :: l, t, h => by
    simp only [tailsOf, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨[], by simp [h]⟩
    · obtain ⟨pre, hp⟩ := mem_tailsOf h; exact ⟨a :: pre, by simp [hp]⟩

inductive LogCheck where
  /-- CHECK, and CHECK-DAG read as CHECK -/
  | has (p : EntryPat)
  /-- a CHECK followed by CHECK-NEXT lines: consecutive entries -/
  | run (ps : List EntryPat)
  /-- `{{regex}}`, an unlabelled line, or a CHECK with CHECK-SAME continuations [native] -/
  | printed (r : Rx)
  deriving Inhabited

def LogCheck.Holds (l : Log) : LogCheck → Prop
  | .has p => ∃ e ∈ l, p.Holds e
  | .run ps => ∃ pre mid post, l = pre ++ mid ++ post ∧ EntryPat.HoldsAll ps mid
  | .printed r => r.search (renderLog l) = true

/-- Do the patterns hold of the first entries of the list, in order? -/
def runAt : List EntryPat → Log → Bool
  | [], _ => true
  | p :: ps, e :: l => p.check e && runAt ps l
  | _ :: _, [] => false

def LogCheck.check (l : Log) : LogCheck → Bool
  | .has p => l.any p.check
  | .run ps => (tailsOf l).any (runAt ps)
  | .printed r => r.search (renderLog l)

theorem runAt_sound : ∀ {ps : List EntryPat} {l : Log}, runAt ps l = true →
    ∃ mid post, l = mid ++ post ∧ EntryPat.HoldsAll ps mid
  | [], l, _ => ⟨[], l, rfl, trivial⟩
  | p :: ps, e :: l, h => by
    simp only [runAt, Bool.and_eq_true] at h
    obtain ⟨mid, post, h1, h2⟩ := runAt_sound h.2
    exact ⟨e :: mid, post, by simp [h1], EntryPat.check_sound h.1, h2⟩
  | _ :: _, [], h => by simp [runAt] at h

theorem LogCheck.check_sound {c : LogCheck} {l : Log} : c.check l = true → c.Holds l := by
  cases c with
  | has p =>
    simp only [LogCheck.check, List.any_eq_true, LogCheck.Holds]
    rintro ⟨e, he, hc⟩; exact ⟨e, he, EntryPat.check_sound hc⟩
  | run ps =>
    simp only [LogCheck.check, List.any_eq_true, LogCheck.Holds]
    rintro ⟨t, ht, hr⟩
    obtain ⟨pre, hpre⟩ := mem_tailsOf ht
    obtain ⟨mid, post, h1, h2⟩ := runAt_sound hr
    exact ⟨pre, mid, post, by rw [← hpre, h1, List.append_assoc], h2⟩
  | printed r => simp [LogCheck.check, LogCheck.Holds]

/-- A phrase evaluates, in some derivation, with a log that meets the checks. -/
def ExpChecks (E : Env) (e : Exp) (cs : List LogCheck) : Prop :=
  ∃ v l, EvalExpL E e v l ∧ ∀ c ∈ cs, c.Holds l

def expChecksB (o : Oracle) (E : Env) (e : Exp) (cs : List LogCheck) : Bool :=
  match evExp o fuelT E e 0 with
  | ⟨.value _, l, _⟩ => cs.all (·.check l)
  | _ => false

theorem expChecks_sound {o : Oracle} {E : Env} {e : Exp} {cs : List LogCheck} :
    expChecksB o E e cs = true → ExpChecks E e cs := by
  unfold expChecksB
  split
  · rename_i v l k h; intro hc
    exact ⟨v, l, evExp_sound_l h, fun c hm => LogCheck.check_sound (List.all_eq_true.mp hc c hm)⟩
  · intro h; cases h

/-! ## A value statement for the ruling theorems -/

def valueCheckB (o : Oracle) (E : Env) (e : Exp) (x : Expect) : Bool :=
  match evExp o fuelT E e 0 with
  | ⟨.value v, _, _⟩ => x.check v
  | _ => false

theorem valueCheck_sound {o : Oracle} {E : Env} {e : Exp} {x : Expect} :
    valueCheckB o E e x = true → ∃ v, EvalExp E e v ∧ x.holds v := by
  unfold valueCheckB; split
  · rename_i v l k h; intro hx; exact ⟨v, evExp_sound (by rw [h]), hx⟩
  · intro h; cases h

/-- The evaluator gives a value without reading a choice, and the value meets `x`: then every
    derivation gives a value meeting `x` (by `evExp_unique`). -/
def uniqueValueB (o : Oracle) (E : Env) (e : Exp) (x : Expect) : Bool :=
  match evExp o fuelT E e 0 with
  | ⟨.value v, _, 0⟩ => x.check v
  | _ => false

theorem uniqueValue_sound {o : Oracle} {E : Env} {e : Exp} {x : Expect} :
    uniqueValueB o E e x = true → (∃ v, EvalExp E e v) ∧ ∀ w, EvalExp E e w → x.holds w := by
  unfold uniqueValueB; split
  · rename_i v l h; intro hx
    exact ⟨⟨v, evExp_sound (by rw [h])⟩, fun w hw => by rw [evExp_unique h w hw]; exact hx⟩
  · intro h; cases h

def checkShowWith (shw : Val → String) (o : Oracle) (E : Env) (e : Exp) (s : String) : Bool :=
  match evExp o fuelT E e 0 with
  | ⟨.value v, _, _⟩ => shw v == s
  | _ => false

theorem checkShowWith_sound {shw : Val → String} {o : Oracle} {E : Env} {e : Exp} {s : String} :
    checkShowWith shw o E e s = true → ∃ v, EvalExp E e v ∧ shw v = s := by
  unfold checkShowWith; split
  · rename_i v l k h; intro hs; exact ⟨v, evExp_sound (by rw [h]), by simpa using hs⟩
  · intro h; cases h

end StandardElm
