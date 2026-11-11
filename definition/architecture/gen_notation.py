# Generates notation.md (beside this script) and ../tex/macros.sty from one table, so they agree one to one.
# Run with --merge to add the chapter requests in requests/*-req.tex.
import datetime
import os
OUT=os.path.dirname(os.path.abspath(__file__))+'/'

# ---------- Syntactic classes: (Class, metavar, macro, expansion, description, level)
SYN = [
 ("SCon","scon","\\scon","\\mv{scon}","special constants","Core"),
 ("Var","var","\\var","\\mv{var}","value variables (lower-case identifiers)","Core"),
 ("Con","con","\\con","\\mv{con}","value constructors (upper-case identifiers)","Core"),
 ("TyVar","tyvar","\\tyvar","\\mv{tyvar}","type variables","Core"),
 ("TyCon","tycon","\\tycon","\\mv{tycon}","type constructors","Core"),
 ("Lab","lab","\\lab","\\mv{lab}","record labels (field names)","Core"),
 ("ModId","modid","\\modid","\\mv{modid}","module identifiers and qualifiers (dotted upper-case names)","Core"),
 ("Op","op","\\opv","\\mv{op}","operator symbols","Core"),
 ("LongVar","longvar","\\longvar","\\mv{longvar}","possibly qualified variables `modid.var`","Core"),
 ("LongCon","longcon","\\longcon","\\mv{longcon}","possibly qualified constructors","Core"),
 ("LongTyCon","longtycon","\\longtycon","\\mv{longtycon}","possibly qualified type constructors","Core"),
 ("AtExp","atexp","\\atexp","\\mv{atexp}","atomic expressions","Core"),
 ("Exp","exp","\\expm","\\mv{exp}","expressions (macro has suffix m: `\\exp` is the exponential)","Core"),
 ("ExpRow","exprow","\\exprow","\\mv{exprow}","expression rows (record fields)","Core"),
 ("Match","match","\\match","\\mv{match}","matches (case branches)","Core"),
 ("MRule","mrule","\\mrule","\\mv{mrule}","match rules","Core"),
 ("Dec","dec","\\dec","\\mv{dec}","declarations (the definitions of a let)","Core"),
 ("ValBind","valbind","\\valbind","\\mv{valbind}","value bindings","Core"),
 ("AtPat","atpat","\\atpat","\\mv{atpat}","atomic patterns","Core"),
 ("Pat","pat","\\pat","\\mv{pat}","patterns","Core"),
 ("PatRow","patrow","\\patrow","\\mv{patrow}","pattern rows (record pattern fields)","Core"),
 ("Ty","ty","\\ty","\\mv{ty}","type expressions","Core"),
 ("TyRow","tyrow","\\tyrow","\\mv{tyrow}","type-expression rows","Core"),
 ("TyVarSeq","tyvarseq","\\tyvarseq","\\mv{tyvarseq}","type-variable sequences (parameters of type declarations)","Modules"),
 ("Module","module","\\modm","\\mv{module}","modules","Modules"),
 ("Header","header","\\header","\\mv{header}","module headers","Modules"),
 ("Imports","imports","\\imports","\\mv{imports}","import lists","Modules"),
 ("ExpList","explist","\\explist","\\mv{explist}","exposing lists","Modules"),
 ("ExpItem","item","\\expitem","\\mv{item}","exposing items","Modules"),
 ("TopDec","topdec","\\topdec","\\mv{topdec}","top-level declarations","Modules"),
 ("DatBind","datbind","\\datbind","\\mv{datbind}","custom-type bindings","Modules"),
 ("ConBind","conbind","\\conbind","\\mv{conbind}","constructor bindings","Modules"),
 ("TypBind","typbind","\\typbind","\\mv{typbind}","type-alias bindings","Modules"),
 ("Program","program","\\program","\\mv{program}","programs","Programs"),
]

# ---------- Semantic classes: (Class, metavar text, macro for class, class expansion, var macro or '' , var expansion, definition, phase, level)
SEM = [
 # static simple
 ("TyVar","alpha or tyvar","\\TyVar","\\cls{TyVar}","",None,"simple; each has a class attribute","static","Core"),
 ("RowVar","epsilon","\\RowVar","\\cls{RowVar}","",None,"simple: row (extension) variables","static","Core"),
 ("TyName","t","\\TyName","\\cls{TyName}","",None,"simple; each has an arity","static","Core"),
 ("Class","kappa","\\Class","\\cls{Class}","",None,"{any, number, comparable, appendable, compappend}","static","Core"),
 ("IdStatus","is","\\IdStatus","\\cls{IdStatus}","\\is","\\mv{is}","{c, v}","static","Core"),
 # static compound
 ("Type","tau","\\Type","\\cls{Type}","",None,"TyVar u RecType u FunType u ConsType","static","Core"),
 ("Row","varrho","\\Row","\\cls{Row}","",None,"Lab ->fin Type","static","Core"),
 ("RecType","(varrho, epsilon) written {varrho | epsilon} or {varrho}","\\RecType","\\cls{RecType}","",None,"Row x (RowVar u {empty})","static","Core"),
 ("FunType","tau -> tau'","\\FunType","\\cls{FunType}","",None,"Type x Type","static","Core"),
 ("ConsType","tau^(k) t","\\ConsType","\\cls{ConsType}","",None,"union over k of Type^k x TyName^(k)","static","Core"),
 ("TypeFcn","theta","\\TypeFcn","\\cls{TypeFcn}","",None,"union over k of (TyVar u RowVar)^k x Type","static","Core"),
 ("TypeScheme","sigma","\\TypeScheme","\\cls{TypeScheme}","",None,"union over k of (TyVar u RowVar)^k x Type","static","Core"),
 ("TyStr","(theta, VE)","\\TyStr","\\cls{TyStr}","",None,"TypeFcn x ValEnv","static","Core"),
 ("TyEnv","TE","\\TyEnv","\\cls{TyEnv}","\\TE","\\mathit{TE}","TyCon ->fin TyStr","static","Core"),
 ("ValEnv","VE","\\ValEnv","\\cls{ValEnv}","\\VE","\\mathit{VE}","static: (Var u Con) ->fin TypeScheme x IdStatus; dynamic: (Var u Con) ->fin Val","both","Core"),
 ("QualEnv","QE","\\QualEnv","\\cls{QualEnv}","\\QE","\\mathit{QE}","ModId ->fin Env (the Env in the range has an empty QE)","both","Core"),
 ("Env","E","\\Env","\\cls{Env}","",None,"static: QualEnv x TyEnv x ValEnv; dynamic: QualEnv x ValEnv","both","Core"),
 ("Context","C","\\Context","\\cls{Context}","",None,"Fin(TyName) x Fin(TyVar u RowVar) x Env, written T, U, E","static","Core"),
 # static modules
 ("Interface","I","\\Interface","\\cls{Interface}","",None,"static: Env (what a module exposes, with exposure of each type); dynamic: Fin(TyCon) x ConEnv x ValEnv, written (RA, CE, VE): exposed record aliases, constructors of each exposed custom type, exposed values (Chapter 7)","both","Modules"),
 ("ModEnv","ME","\\ModEnv","\\cls{ModEnv}","\\ME","\\mathit{ME}","ModId ->fin Interface","both","Modules"),
 ("PortEnv","PE","\\PortEnv","\\cls{PortEnv}","\\PE","\\mathit{PE}","static: Var ->fin Type (port name to declared payload type and direction)","static","Modules"),
 ("Basis","B","\\Basis","\\cls{Basis}","",None,"static: Fin(TyName) x ModEnv x PortEnv, written T, ME, PE; dynamic: ModEnv","both","Modules"),
 # dynamic
 ("SVal","sv","\\SVal","\\cls{SVal}","\\sv","\\mathit{sv}","simple: values of special constants","dynamic","Core"),
 ("BasVal","b","\\BasVal","\\cls{BasVal}","",None,"simple: basic values (names of operations, Appendix D), including the port values outport(p, tau) and inport(p, tau) of Chapter 8","dynamic","Core"),
 ("Val","v","\\Val","\\cls{Val}","",None,"{()} u SVal u BasApp u ConVal u Record u Tuple u Closure u EffVal u JVal (values of type Value are JSON values, Chapter 8)","dynamic","Core"),
 ("BasApp","(b, v1 ... vk)","\\BasApp","\\cls{BasApp}","",None,"BasVal x Val^k, k below the arity of b (partial applications)","dynamic","Core"),
 ("ConVal","con v1 ... vk","\\ConVal","\\cls{ConVal}","",None,"Con x Val^k, k at most the arity of con","dynamic","Core"),
 ("Record","r","\\Record","\\cls{Record}","",None,"Lab ->fin Val","dynamic","Core"),
 ("Tuple","(v1, v2) or (v1, v2, v3)","\\Tuple","\\cls{Tuple}","",None,"Val^2 u Val^3","dynamic","Core"),
 ("Closure","(atpat, exp, E, VE)","\\Closure","\\cls{Closure}","",None,"AtPat x Exp x Env x ValEnv","dynamic","Core"),
 ("FAIL","FAIL","\\FAILcls","\\cls{\\{FAIL\\}}","\\FAIL","\\mathrm{FAIL}","the result of a failed match; not a value","dynamic","Core"),
 # effects
 ("EffVal","ev","\\EffVal","\\cls{EffVal}","\\ev","\\mathit{ev}","TaskVal u CmdVal u SubVal u ProcId u ProgVal","dynamic","Effects"),
 ("TaskVal","tk","\\TaskVal","\\cls{TaskVal}","\\tk","\\mathit{tk}","task values, Chapter 8","dynamic","Effects"),
 ("CmdVal","cm","\\CmdVal","\\cls{CmdVal}","\\cm","\\mathit{cm}","command values, Chapter 8","dynamic","Effects"),
 ("SubVal","sb","\\SubVal","\\cls{SubVal}","\\sbv","\\mathit{sb}","subscription values, Chapter 8","dynamic","Effects"),
 ("ProcId","pid","\\ProcId","\\cls{ProcId}","\\pid","\\mathit{pid}","simple: process identifiers","dynamic","Effects"),
 ("ProgVal","pv","\\ProgVal","\\cls{ProgVal}","\\pv","\\mathit{pv}","program values: {prog} x Record (prog r, made by Platform.worker and the platform's other program makers), Chapter 8","dynamic","Effects"),
 ("JVal","j","\\JVal","\\cls{JVal}","",None,"JSON values: null, Booleans, numbers, strings, arrays, objects","dynamic","Effects"),
 ("Config","K","\\Config","\\cls{Config}","",None,"program configurations, Chapter 9","dynamic","Programs"),
 ("Event","ell","\\Event","\\cls{Event}","",None,"labels of program transitions, Chapter 9","dynamic","Programs"),
]

# ---------- Operations: (name, written, macro, expansion(with #args), nargs, defined in, meaning)
OPS = [
 ("finite maps","A ->fin B","\\finmap","\\xrightarrow{\\mathrm{fin}}",0,"static-core","finite maps; Dom and Ran"),
 ("domain","Dom f","\\Dom","\\mathrm{Dom}\\,",0,"static-core","domain of a finite map"),
 ("range","Ran f","\\Ran","\\mathrm{Ran}\\,",0,"static-core","range of a finite map"),
 ("finite subsets","Fin A","\\Fin","\\mathrm{Fin}\\,",0,"static-core","finite subsets"),
 ("projection","E of C","\\of","\\mathrel{\\mathrm{of}}",0,"static-core","component of a tuple of objects"),
 ("modification","A + B","(plain +)","",-1,"static-core","right map overrides left"),
 ("context extension","C (+) VE","(plain \\oplus)","",-1,"static-core","extend a context, adding type names"),
 ("class order","kappa <= kappa'","(plain \\leq)","",-1,"static-core","number <= comparable, compappend <= comparable, compappend <= appendable, every class <= any"),
 ("admissible types","Adm_kappa","\\Adm","\\mathrm{Adm}_{#1}",1,"static-core","the types a variable of class kappa may stand for"),
 ("class of","cls(alpha)","\\clsof","\\mathrm{class}",0,"static-core","the class attribute of a type variable"),
 ("type variables","tyvars","\\tyvars","\\mathrm{tyvars}\\,",0,"static-core","free type and row variables"),
 ("type names","tynames","\\tynames","\\mathrm{tynames}\\,",0,"static-core","type names occurring in an object"),
 ("instance","sigma > tau","(plain \\succ)","",-1,"static-core","tau is an instance of sigma"),
 ("generalisation","sigma > sigma'","(plain \\succ)","",-1,"static-core","sigma generalises sigma'"),
 ("closure","Clos_C tau","\\Clos","\\mathrm{Clos}",0,"static-core","generalise over variables not free in C"),
 ("type function application","theta(tau1 ... tauk)","(plain)","",-1,"static-core","beta-reduce a type function"),
 ("substitution","S = {tau^(k)/xi^(k)}, written tau{tau^(k)/xi^(k)} or S sigma","(plain)","",-1,"static-core","replace each xi_i by tau_i; respects classes when each tau_i is in Adm_kappa for kappa the class of xi_i; S ranges over substitutions (A95)"),
 ("derivation","D, D'","(plain)","",-1,"static-core","a derivation of a sentence by the rules; D ranges over derivations for one phrase in one context (A95)"),
 ("instance of a derivation","D' an instance of D","(plain)","",-1,"static-core","for some class-respecting S, each type of D' is S applied to the corresponding type of D, each scheme of D' is no more general than S applied to that of D, and S maps U of each context of D onto U of the corresponding context of D' (A95)"),
 ("principal derivation","D principal","(plain)","",-1,"static-core","every derivation for the phrase in the context is an instance of D; legality is judged on it and evaluation follows it (A95, A96)"),
 ("type-name renaming","rho","(plain)","",-1,"static-modules","a bijection from the type names one derivation for a module generates to those another generates; instances of module derivations are taken up to rho (A96)"),
 ("row join","{varrho | epsilon}","\\rec","\\{#1\\}",1,"static-core","closed record type {varrho}"),
 ("open record","{varrho | epsilon}","\\orec","\\{#1 \\mid #2\\}",2,"static-core","open record type"),
 ("constructor type","tau t","(plain)","",-1,"static-core","type construction"),
 ("port payload","Port(tau)","\\Port","\\mathrm{Port}",0,"static-modules","tau may cross a port"),
 ("interface of","Exp(E, explist)","\\Expose","\\mathrm{Expose}",0,"static-modules","interface exposed by an exposing list"),
 ("value of constant","val(scon)","\\valof","\\mathrm{val}",0,"dynamic-core","value denoted by a special constant"),
 ("type of constant","type(scon)","\\typeof","\\mathrm{type}",0,"static-core","type of a special constant"),
 ("apply","APPLY(b, v1 ... vn)","\\APPLY","\\mathrm{APPLY}",0,"appendix-dynamic-basis","the finite set of results of a saturated basic value (a singleton except for equality reaching functions, and empty for Debug.todo)"),
 ("recursive closures","Rec VE","\\Rec","\\mathrm{Rec}\\,",0,"dynamic-core","tie the knot for a recursive group"),
 ("arity","arity(b), arity(con)","\\arity","\\mathrm{arity}",0,"dynamic-core","number of arguments"),
 ("encode","Enc_tau(v)","\\Enc","\\mathrm{Enc}_{#1}",1,"effects","value to JSON at a port"),
 ("decode","Dec_tau(j)","\\Dec","\\mathrm{Dec}_{#1}",1,"effects","JSON to value at a port; partial"),
 ("Int normalisation","norm(n)","\\norm","\\mathrm{norm}",0,"appendix-dynamic-basis","integer into the Int range (Appendix E)"),
 ("Int range","IntRange","\\IntRange","\\mathrm{IntRange}",0,"appendix-dynamic-basis","the implementation's set of Int values (Appendix E)"),
 ("leaf-command sequence","L, c . L","(plain)","",-1,"programs","L ranges over finite sequences of leaf commands, the input of the dispatch sentences s, P, Q, H |- L => (P', Q', H')"),
 ("transition","K --ell--> K'","\\step","\\xrightarrow{#1}",1,"programs","program transition with label"),
 ("static operator table","OT_STAT(op)","\\OTstat","\\mathrm{OT}_{\\mathrm{STAT}}",0,"appendix-static-basis","Op ->fin TypeScheme x IdStatus: the scheme and status of each operator of the initial basis, fixed for every program (audit X1)"),
 ("dynamic operator table","OT_DYN(op)","\\OTdyn","\\mathrm{OT}_{\\mathrm{DYN}}",0,"appendix-dynamic-basis","Op ->fin Val: the value of each operator of the initial basis, fixed for every program (audit X1)"),
]

# ---------- Judgment forms: (phase, level, class, form, macro, pronounced)
JUD = [
 ("static","Core","all Core classes","C |- phrase => A","\\jdg","phrase elaborates to A in context C"),
 ("static","Core","AtPat, Pat, PatRow","C |- pat => (VE, tau)","\\jdg","pat elaborates to VE and tau"),
 ("static","Core","Ty","C |- ty => tau","\\jdg","ty denotes tau in C"),
 ("static","Modules","Module classes","B |- phrase => A","\\jdg","phrase elaborates to A in basis B"),
 ("dynamic","Core","AtExp, Exp, ExpRow, Dec, ValBind","E |- phrase => A","\\jdg","phrase evaluates to A in E"),
 ("dynamic","Core","Match, MRule, AtPat, Pat, PatRow","E, v |- phrase => A","\\jdgv","phrase, matched against v, gives A in E"),
 ("dynamic","Modules","Module classes","B |- phrase => A","\\jdg","phrase evaluates to A in B"),
 ("static","Programs","Program","B |-STAT phrase => A","\\jstat","static judgment used in Chapter 9"),
 ("dynamic","Programs","Program","B |-DYN phrase => A","\\jdyn","dynamic judgment used in Chapter 9"),
 ("static","any","negation","C |- phrase =/=>","\\jnot","phrase does not elaborate"),
]

SPECIAL = [
 ("\\kany","\\mathrm{any}","the unconstrained class"),
 ("\\knum","\\mathrm{number}","class number"),
 ("\\kcomp","\\mathrm{comparable}","class comparable"),
 ("\\kapp","\\mathrm{appendable}","class appendable"),
 ("\\kcapp","\\mathrm{compappend}","class compappend"),
 ("\\isc","\\mathrm{c}","identifier status: constructor"),
 ("\\isv","\\mathrm{v}","identifier status: value"),
 ("\\tInt","\\mathtt{Int}","built-in type name Int"),
 ("\\tFloat","\\mathtt{Float}","built-in type name Float"),
 ("\\tChar","\\mathtt{Char}","built-in type name Char"),
 ("\\tString","\\mathtt{String}","built-in type name String"),
 ("\\tList","\\mathtt{List}","built-in type name List"),
 ("\\tBool","\\mathtt{Bool}","the type name of Bool (a custom type of the basis)"),
 ("\\tunit","\\mathtt{()}","the unit type"),
 ("\\tMaybe","\\mathtt{Maybe}","the type name of Maybe (a custom type of the basis)"),
 ("\\tArray","\\mathtt{Array}","the abstract type name Array of the basis"),
 ("\\tBytes","\\mathtt{Bytes}","the abstract type name Bytes of the basis (elm/bytes), a port payload type (A92)"),
 ("\\tValue","\\mathtt{Value}","the abstract type name Json.Encode.Value (= Json.Decode.Value) of the basis"),
 ("\\emptymap","\\{\\}","the empty map"),
 ("\\emptyrow","\\emptyset","no row variable (closed record type)"),
]

def tex_escape_md(s): return s.replace('|','\\|')
md=[]
md.append("# Notation Registry: A Standard Definition of Elm?\n")
md.append("The single home of every name and symbol in the book. `macros.sty` is generated from this file (with `gen_notation.py`); chapters write registered notation only through its macro. Single-letter metavariables written as plain letters (C, E, T, U, B, D, S) are registered with macro \"(plain)\".\n")
md.append("## Conventions\n")
md.append("- Decorated metavariables (primes, subscripts) range over the same class as the undecorated one.")
md.append("- A sequence x1 ... xk is written x^(k) in the exemplar's style (`x^{(k)}`).")
md.append("- Static and dynamic semantics reuse the names Env, ValEnv, QualEnv, Interface, ModEnv, Basis for their own classes; Chapter 9 distinguishes them as static and dynamic where both are in play.")
md.append("- Syntactic metavariables are italic words set with `\\mv`; terminals are typewriter, set with `\\kw`; classes and semantic domains are roman, set with `\\cls`.")
md.append("- Rows have unique labels: a row variable epsilon in {varrho | epsilon} ranges over rows disjoint from Dom varrho (ruling A23).")
md.append("- Options: first options with `\\opt`, second with `\\optt` (defn.sty).\n")
md.append("## Syntactic Classes\n")
md.append("| Class | Metavariable | Macro | Description | Level |\n|---|---|---|---|---|")
for c,m,mac,exp,d,l in SYN: md.append(f"| {c} | {m} | `{mac}` | {tex_escape_md(d)} | {l} |")
md.append("\n## Semantic Classes\n")
md.append("| Class | Metavariable | Macro (class) | Macro (var) | Definition | Phase | Level |\n|---|---|---|---|---|---|---|")
for c,m,mac,exp,vm,vexp,d,ph,l in SEM:
    md.append(f"| {c} | {tex_escape_md(m)} | `{mac}` | {('`'+vm+'`') if vm else '(plain)'} | {tex_escape_md(d)} | {ph} | {l} |")
md.append("\n## Operations\n")
md.append("| Operation | Written | Macro | Defined In | Meaning (one line) |\n|---|---|---|---|---|")
for n,w,mac,exp,na,di,mean in OPS:
    md.append(f"| {n} | {tex_escape_md(w)} | {('`'+mac+'`') if mac.startswith(chr(92)) else mac} | {di} | {tex_escape_md(mean)} |")
md.append("\n## Judgment Forms\n")
md.append("All sentences use the single relation symbol |-, overloaded over phrase classes as in the exemplar (`\\jdg{A}{phrase}{A'}` prints A |- phrase => A'; `\\jdgv{E}{v}{phrase}{A}` prints E, v |- phrase => A).\n")
md.append("| Phase | Level | Phrase Class | Form | Macro | Pronounced |\n|---|---|---|---|---|---|")
for ph,l,c,f,mac,pr in JUD: md.append(f"| {ph} | {l} | {c} | {tex_escape_md(f)} | `{mac}` | {pr} |")
md.append("\nPer-class judgment boxes (for `\\rulegroup`):\n")
md.append("| Chapter | Group | Box |\n|---|---|---|")
boxes=[("static-core","Atomic Expressions","C |- atexp => tau"),("static-core","Expression Rows","C |- exprow => varrho"),("static-core","Expressions","C |- exp => tau"),("static-core","Matches","C |- match => tau"),("static-core","Match Rules","C |- mrule => tau"),("static-core","Declarations","C |- dec => VE"),("static-core","Value Bindings","C |- valbind => VE"),("static-core","Atomic Patterns","C |- atpat => (VE, tau)"),("static-core","Pattern Rows","C |- patrow => (VE, varrho)"),("static-core","Patterns","C |- pat => (VE, tau)"),("static-core","Type Expressions","C |- ty => tau"),("static-core","Type-expression Rows","C |- tyrow => varrho"),
("dynamic-core","Atomic Expressions","E |- atexp => v"),("dynamic-core","Expression Rows","E |- exprow => r"),("dynamic-core","Expressions","E |- exp => v"),("dynamic-core","Matches","E, v |- match => v'/FAIL"),("dynamic-core","Match Rules","E, v |- mrule => v'/FAIL"),("dynamic-core","Declarations","E |- dec => VE"),("dynamic-core","Value Bindings","E |- valbind => VE"),("dynamic-core","Atomic Patterns","E, v |- atpat => VE/FAIL"),("dynamic-core","Pattern Rows","E, r |- patrow => VE/FAIL"),("dynamic-core","Patterns","E, v |- pat => VE/FAIL")]
for ch,g,b in boxes: md.append(f"| {ch} | {g} | {tex_escape_md(b)} |")
md.append("\nModules, effects and programs chapters define their own boxes with `\\jdg`, `\\jdgv`, `\\jstat`, `\\jdyn`, and record them by adding rows here (stage 02 owns this file).\n")
md.append("## Special Symbols\n")
md.append("| Symbol | Macro | Meaning |\n|---|---|---|")
for mac,exp,mean in SPECIAL: md.append(f"| {exp.replace('|','/')} | `{mac}` | {mean} |")
open(OUT+'notation.md','w').write('\n'.join(md)+'\n')

# ---------- macros.sty
sty=[]
sty.append("\\NeedsTeXFormat{LaTeX2e}")
sty.append(f"\\ProvidesPackage{{macros}}[{datetime.date.today():%Y/%m/%d} Notation for A Standard Definition of Elm?, generated from notation.md]")
sty.append("\\RequirePackage{defn}")
sty.append("% ---- Syntactic classes")
for c,m,mac,exp,d,l in SYN: sty.append(f"\\newcommand{{{mac}}}{{{exp}}} % {c}: {d}")
sty.append("% ---- Semantic classes (class names, and metavariables that need a macro)")
for c,m,mac,exp,vm,vexp,d,ph,l in SEM:
    sty.append(f"\\newcommand{{{mac}}}{{{exp}}} % {c}")
    if vm: sty.append(f"\\newcommand{{{vm}}}{{{vexp}}} % metavariable of {c}")
sty.append("% ---- Operations")
for n,w,mac,exp,na,di,mean in OPS:
    if na<0: continue
    if na==0: sty.append(f"\\newcommand{{{mac}}}{{{exp}}} % {n}")
    else: sty.append(f"\\newcommand{{{mac}}}[{na}]{{{exp}}} % {n}")
sty.append("% ---- Judgment forms")
sty.append("\\newcommand{\\jdg}[3]{#1 \\vdash #2 \\Rightarrow #3} % A |- phrase => A'")
sty.append("\\newcommand{\\jdgv}[4]{#1, #2 \\vdash #3 \\Rightarrow #4} % E, v |- phrase => A")
sty.append("\\newcommand{\\jstat}[3]{#1 \\vdash_{\\mathrm{STAT}} #2 \\Rightarrow #3} % static judgment, Chapter 9")
sty.append("\\newcommand{\\jdyn}[3]{#1 \\vdash_{\\mathrm{DYN}} #2 \\Rightarrow #3} % dynamic judgment, Chapter 9")
sty.append("\\newcommand{\\jnot}[2]{#1 \\vdash #2 \\not\\Rightarrow} % does not elaborate")
sty.append("% ---- Special symbols")
for mac,exp,mean in SPECIAL: sty.append(f"\\newcommand{{{mac}}}{{{exp}}} % {mean}")
# ---------- Merged chapter requests (requests/*-req.tex), reviewed by the orchestrator
import glob, re, sys
MERGE='--merge' in sys.argv
req_md=["\n## Chapter Requests\n","Symbols added by chapter agents through `requests/<chapter>-req.tex`, merged here. The request file is the source of each definition.\n","| Macro | Definition | Registry Row (from the request) | Requested By |","|---|---|---|---|"]
for f in (sorted(glob.glob(OUT+'requests/*-req.tex')) if MERGE else []):
    ch=os.path.basename(f)[:-len('-req.tex')]
    sty.append(f"% ---- requests from {ch}")
    for line in open(f):
        line=line.rstrip('\n')
        if not line.strip(): continue
        sty.append(line)
        m=re.match(r'\\(?:newcommand|DeclareMathOperator)\*?\{?(\\[A-Za-z@]+)\}?(.*?)(?<!\\)%\s*(.*)$', line)
        if m:
            req_md.append(f"| `{m.group(1)}` | `{m.group(2).strip().replace('|','/')}` | {m.group(3).replace('|','/')} | {ch} |")
if MERGE: open(OUT+'notation.md','a').write('\n'.join(req_md)+'\n')
sty.append("\\endinput")
open(os.path.join(OUT,'..','tex','macros.sty'),'w').write('\n'.join(sty)+'\n')
print(len(SYN),len(SEM),len(OPS),len(JUD),len(SPECIAL))
