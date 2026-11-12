/-
  A Standard Definition of Elm? Mechanisation: printing certificates as Lean terms, plan step 9
  (section 13). Used by `lake exe certify` only; the printed term is read back by Lean, so a
  mistake here can only make a certificate fail to elaborate or to check.
-/
import StandardElmMech.Stat.Annotated

namespace StandardElm.Stat.Print
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BTyRow BAtPat BPatRow BPat BAtExp BExpRow BExp BMatch BMRule BDec BValBind
  SLit BItem BExpList BImport BConBind BDatBind BTypBind BTopDec BHeader BModule)

def q (s : String) : String := s.quote

def paren (s : String) : String := "(" ++ s ++ ")"

def list {α : Type} (f : α → String) (xs : List α) : String := "[" ++ ", ".intercalate (xs.map f) ++ "]"

def opt {α : Type} (f : α → String) : Option α → String
  | none => "none"
  | some x => paren ("some " ++ f x)

def cls : Cls → String
  | .any => ".any" | .num => ".num" | .comp => ".comp" | .app => ".app" | .capp => ".capp"

def tyVar : TyVar → String
  | .named s => paren (".named " ++ q s)
  | .fresh n c => paren (".fresh " ++ toString n ++ " " ++ cls c)
  | .bnd i c => paren (".bnd " ++ toString i ++ " " ++ cls c)

def rowVar : RowVar → String
  | .named s => paren (".named " ++ q s)
  | .fresh n => paren (".fresh " ++ toString n)
  | .bnd i => paren (".bnd " ++ toString i)

def bvar : BVar → String
  | .ty a => paren (".ty " ++ tyVar a)
  | .row e => paren (".row " ++ rowVar e)

def tyName (t : TyName) : String :=
  let names := [(tInt, "tInt"), (tFloat, "tFloat"), (tChar, "tChar"), (tString, "tString"), (tUnit, "tUnit"),
    (tList, "tList"), (tTuple2, "tTuple2"), (tTuple3, "tTuple3"), (tBool, "tBool"), (tOrder, "tOrder"),
    (tNever, "tNever"), (tMaybe, "tMaybe"), (tResult, "tResult"), (tArray, "tArray"), (tBytes, "tBytes"),
    (tValue, "tValue"), (tCmd, "tCmd"), (tSub, "tSub"), (tTask, "tTask"), (tProcessId, "tProcessId"),
    (tProgram, "tProgram"), (tNode, "tNode")]
  match names.find? (·.1 == t) with
  | some (_, n) => n
  | none => paren ("TyName.mk " ++ toString t.id ++ " " ++ toString t.arity)

partial def ty : Ty → String
  | .var (.fresh n c) => paren (".var (.fresh " ++ toString n ++ " " ++ cls c ++ ")")
  | .var a => paren (".var " ++ tyVar a)
  | .record ρ tl => paren (".record " ++ list (fun p => paren (q p.1 ++ ", " ++ ty p.2)) ρ ++ " " ++ opt rowVar tl)
  | .fn a b => paren (".fn " ++ ty a ++ " " ++ ty b)
  | .con [] t =>
    if t == tInt then "tIntTy" else if t == tFloat then "tFloatTy" else if t == tString then "tStringTy"
    else if t == tChar then "tCharTy" else if t == tUnit then "tUnitTy"
    else paren (".con [] " ++ tyName t)
  | .con as t => paren (".con " ++ list ty as ++ " " ++ tyName t)

def status : IdStatus → String
  | .c => ".c" | .v => ".v"

def scheme (σ : Scheme) : String := "⟨" ++ list bvar σ.bound ++ ", " ++ ty σ.body ++ "⟩"

def valEnv (VE : ValEnv) : String :=
  list (fun p => paren (q p.1 ++ ", (" ++ scheme p.2.1 ++ ", " ++ status p.2.2 ++ ")")) VE

def tyFcn (θ : TyFcn) : String := "⟨" ++ list bvar θ.params ++ ", " ++ ty θ.body ++ "⟩"

def tyEnv (TE : TyEnv) : String :=
  list (fun p => paren (q p.1 ++ ", (" ++ tyFcn p.2.1 ++ ", " ++ valEnv p.2.2 ++ ")")) TE

def ienv (I : IEnv) : String := "⟨" ++ tyEnv I.TE ++ ",\n    " ++ valEnv I.VE ++ "⟩"

def env (E : Env) : String :=
  "⟨" ++ list (fun p => paren (q p.1 ++ ", " ++ ienv p.2)) E.QE ++ ",\n  " ++ tyEnv E.TE ++ ",\n  " ++ valEnv E.VE ++ "⟩"

def ctx (C : Ctx) : String := "⟨" ++ list tyName C.T ++ ", " ++ list bvar C.U ++ ",\n  " ++ env C.E ++ "⟩"

def longId (l : LongId) : String := "⟨" ++ opt q l.qual ++ ", " ++ q l.id ++ "⟩"

def slit : SLit → String
  | .int n => paren (".int " ++ toString n)
  | .float m e => paren (".float " ++ toString m ++ " " ++ paren (toString e))
  | .char c => paren (".char " ++ c.quote)
  | .str s => paren (".str " ++ q s)

/-! ## Bare phrases kept in certificates -/

mutual
partial def bty : BTy → String
  | .tyvar a => paren (".tyvar " ++ q a)
  | .record row => paren (".record " ++ opt btyRow row)
  | .openRecord r row => paren (".openRecord " ++ q r ++ " " ++ btyRow row)
  | .unit => ".unit"
  | .tuple t1 t2 t3 => paren (".tuple " ++ bty t1 ++ " " ++ bty t2 ++ " " ++ opt bty t3)
  | .con c args => paren (".con " ++ longId c ++ " " ++ list bty args)
  | .fn a b => paren (".fn " ++ bty a ++ " " ++ bty b)
  | .paren t => paren (".paren " ++ bty t)
partial def btyRow : BTyRow → String
  | .field l t rest => paren (".field " ++ q l ++ " " ++ bty t ++ " " ++ opt btyRow rest)
end

def item : BItem → String
  | .var x => paren (".var " ++ q x)
  | .op o => paren (".op " ++ q o)
  | .ty c => paren (".ty " ++ q c)
  | .tyAll c => paren (".tyAll " ++ q c)

def expList : BExpList → String
  | .all => ".all"
  | .items is => paren (".items " ++ list item is)

def bimport (i : BImport) : String := "⟨" ++ q i.mod ++ ", " ++ opt q i.alias ++ ", " ++ opt expList i.exposing ++ "⟩"

def header (h : BHeader) : String := "⟨" ++ toString h.isPort ++ ", " ++ q h.name ++ ", " ++ expList h.exposing ++ "⟩"

def datBind (d : BDatBind) : String :=
  list (fun c => paren (q c.1 ++ ", " ++ list q c.2.1 ++ ", " ++ list (fun k => paren (q k.1 ++ ", " ++ list bty k.2)) c.2.2)) d

def typBind (tb : BTypBind) : String := "⟨" ++ q tb.c ++ ", " ++ list q tb.params ++ ", " ++ bty tb.t ++ "⟩"

/-! ## Annotated phrases -/

mutual
partial def atPat : AAtPat → String
  | .wild τ => paren (".wild " ++ ty τ)
  | .scon sc τ => paren (".scon " ++ slit sc ++ " " ++ ty τ)
  | .var x τ => paren (".var " ++ q x ++ " " ++ ty τ)
  | .con lc inst τ => paren (".con " ++ longId lc ++ " " ++ list ty inst ++ " " ++ ty τ)
  | .unit => ".unit"
  | .tuple p1 p2 p3 => paren (".tuple " ++ pat p1 ++ " " ++ pat p2 ++ " " ++ opt pat p3)
  | .nil τ => paren (".nil " ++ ty τ)
  | .record row τ => paren (".record " ++ opt patRow row ++ " " ++ ty τ)
  | .paren p => paren (".paren " ++ pat p)
partial def patRow : APatRow → String
  | .field l τ rest => paren (".field " ++ q l ++ " " ++ ty τ ++ " " ++ opt patRow rest)
partial def pat : APat → String
  | .atpat a => paren (".atpat " ++ atPat a)
  | .con lc inst args τ => paren (".con " ++ longId lc ++ " " ++ list ty inst ++ " " ++ list atPat args ++ " " ++ ty τ)
  | .cons p1 p2 => paren (".cons " ++ pat p1 ++ " " ++ pat p2)
  | .as p x => paren (".as " ++ pat p ++ " " ++ q x)
end

mutual
partial def atExp : AAtExp → String
  | .scon sc τ => paren (".scon " ++ slit sc ++ " " ++ ty τ)
  | .var lv inst τ => paren (".var " ++ longId lv ++ " " ++ list ty inst ++ " " ++ ty τ)
  | .con lc inst τ => paren (".con " ++ longId lc ++ " " ++ list ty inst ++ " " ++ ty τ)
  | .op o inst τ => paren (".op " ++ q o ++ " " ++ list ty inst ++ " " ++ ty τ)
  | .unit => ".unit"
  | .tuple e1 e2 e3 => paren (".tuple " ++ exp e1 ++ " " ++ exp e2 ++ " " ++ opt exp e3)
  | .nil τ => paren (".nil " ++ ty τ)
  | .record row => paren (".record " ++ opt expRow row)
  | .update x inst τ row => paren (".update " ++ q x ++ " " ++ list ty inst ++ " " ++ ty τ ++ " " ++ expRow row)
  | .letE d e => paren (".letE " ++ dec d ++ " " ++ exp e)
  | .paren e => paren (".paren " ++ exp e)
partial def expRow : AExpRow → String
  | .field l e rest => paren (".field " ++ q l ++ " " ++ exp e ++ " " ++ opt expRow rest)
partial def exp : AExp → String
  | .atexp a => paren (".atexp " ++ atExp a)
  | .app e a => paren (".app " ++ exp e ++ " " ++ atExp a)
  | .lam p e => paren (".lam " ++ atPat p ++ " " ++ exp e)
  | .caseE e m => paren (".caseE " ++ exp e ++ " " ++ «match» m)
partial def «match» : AMatch → String
  | .mk (.mk p e) rest => paren (".mk (.mk " ++ pat p ++ " " ++ exp e ++ ") " ++ opt «match» rest)
partial def dec : ADec → String
  | .val VE vb => paren (".val " ++ valEnv VE ++ " " ++ valBind vb)
partial def valBind : AValBind → String
  | .var x ann τ e rest =>
    paren (".var " ++ q x ++ " " ++ opt (fun p => paren (bty p.1 ++ ", " ++ list bvar p.2)) ann ++ " " ++ ty τ ++ " " ++
      exp e ++ " " ++ opt valBind rest)
  | .pat p e => paren (".pat " ++ atPat p ++ " " ++ exp e)
end

partial def topDec : ATopDec → String
  | .value VE vb => paren (".value " ++ valEnv VE ++ " " ++ valBind vb)
  | .types TE VE db tbs => paren (".types " ++ tyEnv TE ++ " " ++ valEnv VE ++ " " ++ opt datBind db ++ " " ++ list typBind tbs)
  | .typesSplit a1 a2 => paren (".typesSplit " ++ topDec a1 ++ " " ++ topDec a2)
  | .port x t U => paren (".port " ++ q x ++ " " ++ bty t ++ " " ++ list bvar U)
  | .seq a1 a2 => paren (".seq\n    " ++ topDec a1 ++ "\n    " ++ topDec a2)

def item' : BItem → String := item

def imports (is : List BImport) : String := list bimport is

def amodule (a : AModule) : String :=
  "⟨" ++ header a.header ++ ",\n    " ++ list bimport a.imports ++ ",\n    " ++ opt topDec a.body ++ "⟩"

def aprogram (a : AProgram) : String := "[" ++ ",\n  ".intercalate (a.map amodule) ++ "]"

end StandardElm.Stat.Print
