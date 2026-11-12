/-
  `lake exe compare-derived` (plan step 8, section 3.4): for every program translated today, its
  modules as the translator builds them (module form, Mod/Program.lean) against the derived forms of
  its source syntax (`Src.deriveModule`), compared in a neutral form: annotations dropped, integer
  constants as `num n` whatever their specialisation, the suffix `$...` of the translator's
  specialisation copies removed, and, in each chain of `let`s and among a module's top-level
  definitions, a binding of a name already bound by an earlier binding of the chain with an equal
  right-hand side removed (the copies collapse to the default copy). For each module, the value
  definitions (name and right-hand side) and the grouping (the names of each group) are compared.
-/
import StandardElmMech.AllPrograms
import StandardElmMech.Generated.SrcAll
import StandardElmMech.Src.Derive
import StandardElmMech.WorkerTheorems

open StandardElm StandardElm.Src

def stripCopy (x : String) : String := (x.splitOn "$").headD x

/-- A long identifier without its qualifier: the translator resolves an exposed name to its
    qualified form, which is elaboration's business, not a derived form's. -/
def showLong (l : LongId) : String := stripCopy l.id

/-! ## The reduced syntax -/

def rSCon : SCon → String
  | .int n => s!"num {n}"
  | .intF n => s!"num {n}"
  | .float m e => s!"float {m} {e}"
  | .char c => s!"char {c.toNat}"
  | .str s => s!"str {repr s}"

mutual
  partial def rAP : AtPat → String
    | .wild => "_"
    | .scon s => rSCon s
    | .var x => stripCopy x
    | .con c => showLong c
    | .unit => "()"
    | .tuple a b c => s!"({rP a}, {rP b}{(c.map (", " ++ rP ·)).getD ""})"
    | .nil => "[]"
    | .record r => "{" ++ rPRow r ++ "}"
    | .paren p => s!"({rP p})"
  partial def rPRow : Option PatRow → String
    | none => ""
    | some (.field l r) => l ++ (if r.isSome then ", " else "") ++ rPRow r
  partial def rP : Pat → String
    | .atpat a => rAP a
    | .con c as => s!"{showLong c} {" ".intercalate (as.map rAP)}"
    | .cons a b => s!"{rP a} :: {rP b}"
    | .as p x => s!"{rP p} as {x}"
end

mutual
  partial def rA (ctx : List (String × String)) : AtExp → String
    | .scon s => rSCon s
    | .var l => showLong l
    | .con l => showLong l
    | .op o => s!"({o})"
    | .unit => "()"
    | .tuple a b c => s!"({rE [] a}, {rE [] b}{(c.map (", " ++ rE [] ·)).getD ""})"
    | .nil => "[]"
    | .record r => "{" ++ rRow r ++ "}"
    | .update x r => "{" ++ x ++ " | " ++ rRow (some r) ++ "}"
    | .letE (.val vb) body =>
      let bs := rBinds vb
      let kept := bs.filter fun b => !(ctx.contains b)
      let inner := rE (ctx ++ bs) body
      if kept.isEmpty then inner
      else "let " ++ " and ".intercalate (kept.map fun (x, e) => x ++ " = " ++ e) ++ " in " ++ inner
    | .paren e => s!"({rE [] e})"
  partial def rRow : Option ExpRow → String
    | none => ""
    | some (.field l e r) => l ++ " = " ++ rE [] e ++ (if r.isSome then ", " else "") ++ rRow r
  partial def rE (ctx : List (String × String)) : Exp → String
    | .atexp a => rA ctx a
    | .app f a => s!"{rE [] f} {rA [] a}"
    | .lam p e => s!"\\{rAP p} -> {rE [] e}"
    | .caseE e m => s!"case {rE [] e} of {rM m}"
  partial def rM : Match → String
    | .mk (.mk p e) none => s!"{rP p} -> {rE [] e}"
    | .mk (.mk p e) (some r) => s!"{rP p} -> {rE [] e}; {rM r}"
  partial def rBinds : ValBind → List (String × String)
    | .var x e r => (stripCopy x, rE [] e) :: ((r.map rBinds).getD [])
    | .pat p e => [("pat " ++ rAP p, rE [] e)]
end

/-! ## The bare syntax -/

def bLit : SLit → String
  | .int n => s!"num {n}"
  | .float m e => s!"float {m} {e}"
  | .char c => s!"char {c.toNat}"
  | .str s => s!"str {repr s}"

mutual
  partial def bAP : BAtPat → String
    | .wild => "_"
    | .scon s => bLit s
    | .var x => x
    | .con c => showLong c
    | .unit => "()"
    | .tuple a b c => s!"({bP a}, {bP b}{(c.map (", " ++ bP ·)).getD ""})"
    | .nil => "[]"
    | .record r => "{" ++ bPRow r ++ "}"
    | .paren p => s!"({bP p})"
  partial def bPRow : Option BPatRow → String
    | none => ""
    | some (.field l r) => l ++ (if r.isSome then ", " else "") ++ bPRow r
  partial def bP : BPat → String
    | .atpat a => bAP a
    | .con c as => s!"{showLong c} {" ".intercalate (as.map bAP)}"
    | .cons a b => s!"{bP a} :: {bP b}"
    | .as p x => s!"{bP p} as {x}"
end

mutual
  partial def bA (ctx : List (String × String)) : BAtExp → String
    | .scon s => bLit s
    | .var l => showLong l
    | .con l => showLong l
    | .op o => s!"({o})"
    | .unit => "()"
    | .tuple a b c => s!"({bE [] a}, {bE [] b}{(c.map (", " ++ bE [] ·)).getD ""})"
    | .nil => "[]"
    | .record r => "{" ++ bRow r ++ "}"
    | .update x r => "{" ++ x ++ " | " ++ bRow (some r) ++ "}"
    | .letE (.val vb) body =>
      let bs := bBinds vb
      let kept := bs.filter fun b => !(ctx.contains b)
      let inner := bE (ctx ++ bs) body
      if kept.isEmpty then inner
      else "let " ++ " and ".intercalate (kept.map fun (x, e) => x ++ " = " ++ e) ++ " in " ++ inner
    | .paren e => s!"({bE [] e})"
  partial def bRow : Option BExpRow → String
    | none => ""
    | some (.field l e r) => l ++ " = " ++ bE [] e ++ (if r.isSome then ", " else "") ++ bRow r
  partial def bE (ctx : List (String × String)) : BExp → String
    | .atexp a => bA ctx a
    | .app f a => s!"{bE [] f} {bA [] a}"
    | .lam p e => s!"\\{bAP p} -> {bE [] e}"
    | .caseE e m => s!"case {bE [] e} of {bM m}"
  partial def bM : BMatch → String
    | .mk (.mk p e) none => s!"{bP p} -> {bE [] e}"
    | .mk (.mk p e) (some r) => s!"{bP p} -> {bE [] e}; {bM r}"
  partial def bBinds : BValBind → List (String × String)
    | .var x _ e r => (x, bE [] e) :: ((r.map bBinds).getD [])
    | .pat p e => [("pat " ++ bAP p, bE [] e)]
end

/-! ## Modules -/

/-- The value groups of a module, each a list of (name, right-hand side). -/
partial def rGroups : Mod.TopDec → List (List (String × String))
  | .val vb => [vb.map fun (x, e) => (stripCopy x, rE [] e)]
  | .seq a b => rGroups a ++ rGroups b
  | _ => []

partial def bGroups : BTopDec → List (List (String × String))
  | .value vb => [bBinds vb]
  | .seq a b => bGroups a ++ bGroups b
  | _ => []

/-- Collapse copies: drop a binding equal (name and right-hand side) to an earlier one; drop
    groups left empty; then sort the groups and their members, for a comparison up to order. -/
def normalise (gs : List (List (String × String))) : List (List (String × String)) := Id.run do
  let mut seen : List (String × String) := []
  let mut out : List (List (String × String)) := []
  for g in gs do
    let kept := g.filter fun b => !(seen.contains b)
    seen := seen ++ g
    if !kept.isEmpty then out := out ++ [kept.mergeSort (fun a b => a.1 ≤ b.1)]
  return out.mergeSort (fun a b => (a.headD ("", "")).1 ≤ (b.headD ("", "")).1)

def main : IO UInt32 := do
  let srcByKey : List ((String × String) × SProgram) :=
    srcShards.flatMap fun (_, ps) => ps.map fun (n, p) => ((p.project, n), p)
  let translated : List Program := allPrograms ++ generatedWorkers.map (·.prog)
  let mut programs := 0
  let mut modules := 0
  let mut differ := 0
  let mut missing : Array String := #[]
  let mut shown := 0
  for p in translated do
    let project := match p.source.splitOn "/" with
      | "tests" :: proj :: _ => proj
      | _ => ""
    match srcByKey.lookup (project, p.name) with
    | none => missing := missing.push p.name
    | some s =>
      programs := programs + 1
      let bms := (deriveProgram s).modules
      for m in p.modules do
        match bms.find? (·.header.name == m.header.modid) with
        | none => missing := missing.push s!"{p.name}:{m.header.modid}"
        | some bm =>
          modules := modules + 1
          let r := normalise (rGroups m.body)
          let b := normalise ((bm.body.map bGroups).getD [])
          if r != b then
            differ := differ + 1
            if shown < 5 then
              shown := shown + 1
              IO.println s!"DIFFER {p.name} module {m.header.modid}:"
              let rf := r.flatten
              let bf := b.flatten
              for x in rf do
                if !(bf.contains x) then
                  match bf.lookup x.1 with
                  | some y =>
                    let common := (x.2.toList.zip y.toList).takeWhile (fun (a, b) => a == b) |>.length
                    IO.println s!"  {x.1}: translation …{(x.2.drop (common - 60)).take 160}"
                    IO.println s!"  {x.1}: derived     …{(y.drop (common - 60)).take 160}"
                  | none => IO.println s!"  {x.1}: only in the translation"
              for x in bf do
                if !(rf.any (·.1 == x.1)) then IO.println s!"  {x.1}: only in the derived forms"
  IO.println s!"{programs} programs, {modules} modules compared, {differ} differ."
  if !missing.isEmpty then IO.println s!"not found in the source syntax: {missing.toList}"
  return (if differ == 0 then 0 else 1)
