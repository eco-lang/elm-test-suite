/-
  A Standard Definition of Elm? Mechanisation: every module of the proved algorithm W of plan
  step 11 (milestones (b) to (e)): the substitution algebra, the most general unifier without
  and with classes, W, its soundness, refutation, completeness, principality and termination, the
  fragments, and the unit examples; for milestone (d), substitutions of row variables, unification
  with rows (the mgu theorem and termination), W for records (`inferExpWD`: soundness,
  termination, the main induction L11 and refutation `wdRefutation`) and its examples; for
  milestone (e), W with annotations naming type variables (`WE.inferExpWD`), its examples, and its
  principality (`WE.wePrincipality`, `WE.inferExpWD_principal`); for milestone (f), W for modules
  and programs (`MW.inferModuleW`, `MW.inferProgramW`), their refutation (`MW.inferModuleW_fail`,
  `MW.inferProgramW_fail`, `Stat.not_legal_of_wRefutes`) and principality
  (`MW.inferModuleW_principal`, `MW.inferProgramW_principal`), with ports (milestone (g),
  `ModulesPorts.lean`); for milestone (g), the discharge of D11 per test (`Discharge.lean`:
  `Stat.wCheck`, `Stat.legal_of_W`, `Stat.ident_of_wCheck`, `Stat.programSem_of_wCheck`,
  `Stat.not_legal_of_wMainVar`).
  Importable together with milestone (a)'s core chain (`CoreComplete`).
-/
import StandardElmMech.Stat.Complete.FSubst
import StandardElmMech.Stat.Complete.Mgu
import StandardElmMech.Stat.Complete.MguTerm
import StandardElmMech.Stat.Complete.MguCls
import StandardElmMech.Stat.Complete.MguC
import StandardElmMech.Stat.Complete.MguCLoop
import StandardElmMech.Stat.Complete.MguCVars
import StandardElmMech.Stat.Complete.W
import StandardElmMech.Stat.Complete.Fragment
import StandardElmMech.Stat.Complete.InstCounter
import StandardElmMech.Stat.Complete.WPrincipal
import StandardElmMech.Stat.Complete.WBasics
import StandardElmMech.Stat.Complete.WRel
import StandardElmMech.Stat.Complete.WState
import StandardElmMech.Stat.Complete.Canon
import StandardElmMech.Stat.Complete.Closure
import StandardElmMech.Stat.Complete.WPhrase
import StandardElmMech.Stat.Complete.WUnify
import StandardElmMech.Stat.Complete.WCompletePat
import StandardElmMech.Stat.Complete.WCompleteAux
import StandardElmMech.Stat.Complete.WComplete
import StandardElmMech.Stat.Complete.WTheorems
import StandardElmMech.Stat.Complete.WNodeClos
import StandardElmMech.Stat.Complete.WNodes
import StandardElmMech.Stat.Complete.WNodeRel
import StandardElmMech.Stat.Complete.WNodeRelExp
import StandardElmMech.Stat.Complete.WPrincipality
import StandardElmMech.Stat.Complete.WTerm
import StandardElmMech.Stat.Complete.WSoundBase
import StandardElmMech.Stat.Complete.WSoundPost
import StandardElmMech.Stat.Complete.WSoundClos
import StandardElmMech.Stat.Complete.WSoundPat
import StandardElmMech.Stat.Complete.WSoundAux
import StandardElmMech.Stat.Complete.WSoundExp
import StandardElmMech.Stat.Complete.WSound
import StandardElmMech.Stat.Complete.WExamples
import StandardElmMech.Stat.Complete.WExamplesC
import StandardElmMech.Stat.Complete.RowAlg
import StandardElmMech.Stat.Complete.RSubst
import StandardElmMech.Stat.Complete.MguR
import StandardElmMech.Stat.Complete.MguRRows
import StandardElmMech.Stat.Complete.MguRCases
import StandardElmMech.Stat.Complete.MguRRec
import StandardElmMech.Stat.Complete.MguRBind
import StandardElmMech.Stat.Complete.MguRTwo
import StandardElmMech.Stat.Complete.MguRStep
import StandardElmMech.Stat.Complete.MguRLoop
import StandardElmMech.Stat.Complete.MguRTerm
import StandardElmMech.Stat.Complete.MguRExamples
import StandardElmMech.Stat.Complete.WD
import StandardElmMech.Stat.Complete.WDTerm
import StandardElmMech.Stat.Complete.WDUnify
import StandardElmMech.Stat.Complete.WExamplesD
import StandardElmMech.Stat.Complete.WDBridge
import StandardElmMech.Stat.Complete.WDBasics
import StandardElmMech.Stat.Complete.WDRel
import StandardElmMech.Stat.Complete.WDState
import StandardElmMech.Stat.Complete.WDClosure
import StandardElmMech.Stat.Complete.WDPhrase
import StandardElmMech.Stat.Complete.WDUnifyW
import StandardElmMech.Stat.Complete.WDRows
import StandardElmMech.Stat.Complete.WDCompletePat
import StandardElmMech.Stat.Complete.WDCompleteAux
import StandardElmMech.Stat.Complete.WDComplete
import StandardElmMech.Stat.Complete.WDTheorems
import StandardElmMech.Stat.Complete.WDNodeDef
import StandardElmMech.Stat.Complete.WDNodeClos
import StandardElmMech.Stat.Complete.WDNodeRel
import StandardElmMech.Stat.Complete.WDNodeRelExp
import StandardElmMech.Stat.Complete.WDNodeOk
import StandardElmMech.Stat.Complete.WDPrincipality
import StandardElmMech.Stat.Complete.WDSoundMgu
import StandardElmMech.Stat.Complete.WDSoundBase
import StandardElmMech.Stat.Complete.WDSoundClos
import StandardElmMech.Stat.Complete.WDSoundInst
import StandardElmMech.Stat.Complete.WDSoundPat
import StandardElmMech.Stat.Complete.WDSoundPats
import StandardElmMech.Stat.Complete.WDSoundAux
import StandardElmMech.Stat.Complete.WDSoundExp
import StandardElmMech.Stat.Complete.WDSound
import StandardElmMech.Stat.Complete.WE
import StandardElmMech.Stat.Complete.WEExamples
import StandardElmMech.Stat.Complete.WETerm
import StandardElmMech.Stat.Complete.WEPhrase
import StandardElmMech.Stat.Complete.WECompleteAux
import StandardElmMech.Stat.Complete.WEComplete
import StandardElmMech.Stat.Complete.WETheorems
import StandardElmMech.Stat.Complete.WENodeRel
import StandardElmMech.Stat.Complete.WENodeRelExp
import StandardElmMech.Stat.Complete.WEPrincipality
import StandardElmMech.Stat.Complete.CheckedDeriv
import StandardElmMech.Stat.Complete.Modules
import StandardElmMech.Stat.Complete.ModulesCongr
import StandardElmMech.Stat.Complete.ModulesFail
import StandardElmMech.Stat.Complete.ModulesPorts
import StandardElmMech.Stat.Complete.ModulesNodes
import StandardElmMech.Stat.Complete.ModulesPrincipalExp
import StandardElmMech.Stat.Complete.ModulesPrincipal
import StandardElmMech.Stat.Complete.ModulesProgram
import StandardElmMech.Stat.Complete.Discharge
