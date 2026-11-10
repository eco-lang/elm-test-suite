module DerivedForms.Table exposing (rows)

{-| The derived forms of Appendix A of A Standard Definition of Elm?: the single source from which
`GenerateDerivedForms.elm` writes the tables of `definition/tex/appendix-derived-forms.tex` and the
derived-form functions of `Derived.lean`. To change a derived form, change its row here and run the
generator; never edit the generated regions.

In a sequence row, the Lean sequence parameter always comes first.

-}

import DerivedForms.Term exposing (..)


sp : Piece
sp =
    Raw "\\ "


exp1 : Ref
exp1 =
    Indexed Exp 1


exp2 : Ref
exp2 =
    Indexed Exp 2


exp3 : Ref
exp3 =
    Indexed Exp 3


rows : List Row
rows =
    [ { label = "df:infix"
      , block = Expressions
      , derived = [ M exp1, sp, M (Plain Opv), sp, M exp2 ]
      , equivalent = Template (TApp (TApp (TOp (Plain Opv)) (TParen (TMeta exp1))) (TParen (TMeta exp2)))
      , condition = NoCondition
      , lean =
            Generated
                { name = "bin"
                , params = [ { name = "o", ref = Plain Opv }, { name = "e1", ref = exp1 }, { name = "e2", ref = exp2 } ]
                , result = Exp
                , seqParam = Nothing
                , whenEmpty = Nothing
                }
      }
    , { label = "df:if"
      , block = Expressions
      , derived = [ Kw "if", sp, M exp1, sp, Kw "then", sp, M exp2, sp, Kw "else", sp, M exp3 ]
      , equivalent =
            Template
                (TCase (TMeta exp1)
                    [ ( TConQual "Basics" "True", TParen (TMeta exp2) )
                    , ( TConQual "Basics" "False", TMeta exp3 )
                    ]
                )
      , condition = NoCondition
      , lean =
            Generated
                { name = "ifte"
                , params = [ { name = "e1", ref = exp1 }, { name = "e2", ref = exp2 }, { name = "e3", ref = exp3 } ]
                , result = Exp
                , seqParam = Nothing
                , whenEmpty = Nothing
                }
      }
    , { label = "df:if-chain"
      , block = Expressions
      , derived =
            [ Raw "\\begin{array}[t]{@{}l@{}}\n         \\kw{if}\\ \\expm_1\\ \\kw{then}\\ \\expm'_1\\\\\n         \\kw{else}\\ \\kw{if}\\ \\expm_2\\ \\kw{then}\\ \\expm'_2\\ \\cdots\\\\\n         \\kw{else}\\ \\kw{if}\\ \\expm_n\\ \\kw{then}\\ \\expm'_n\\\\\n         \\kw{else}\\ \\expm\n       \\end{array}" ]
      , equivalent =
            Template
                (TNestRight
                    { item = TUse "df:if" [ TMeta (Item Exp), TMeta (ItemPrimed Exp), THole ]
                    , base = TMeta (Plain Exp)
                    , wrapInner = True
                    , showSecond = True
                    , layout = Lines { indent = "\\;", afterSecond = "\\ \\cdots", closing = "\\ \\kw{)}\\cdots\\kw{)}" }
                    }
                )
      , condition = LastLine "\\qquad (n\\geq 2)"
      , lean =
            Generated
                { name = "ifChain"
                , params = [ { name = "e", ref = Plain Exp } ]
                , result = Exp
                , seqParam = Just { name = "arms", items = [ Item Exp, ItemPrimed Exp ] }
                , whenEmpty = Nothing
                }
      }
    , { label = "df:and"
      , block = Expressions
      , derived = [ M exp1, sp, Kw "\\&\\&", sp, M exp2 ]
      , equivalent = Template (TUse "df:if" [ TMeta exp1, TMeta exp2, TConQual "Basics" "False" ])
      , condition = NoCondition
      , lean =
            Generated
                { name = "andalso"
                , params = [ { name = "e1", ref = exp1 }, { name = "e2", ref = exp2 } ]
                , result = Exp
                , seqParam = Nothing
                , whenEmpty = Nothing
                }
      }
    , { label = "df:or"
      , block = Expressions
      , derived = [ M exp1, sp, Kw "||", sp, M exp2 ]
      , equivalent = Template (TUse "df:if" [ TMeta exp1, TConQual "Basics" "True", TMeta exp2 ])
      , condition = NoCondition
      , lean =
            Generated
                { name = "orelse"
                , params = [ { name = "e1", ref = exp1 }, { name = "e2", ref = exp2 } ]
                , result = Exp
                , seqParam = Nothing
                , whenEmpty = Nothing
                }
      }
    , { label = "df:lambda-params"
      , block = Expressions
      , derived = [ Kw "\\textbackslash", Raw "\\atpat_1\\cdots\\atpat_n", sp, Kw "->", sp, M (Plain Exp) ]
      , equivalent =
            Template
                (TNestRight
                    { item = TLam (TMeta (Item AtPat)) THole
                    , base = TMeta (Plain Exp)
                    , wrapInner = False
                    , showSecond = False
                    , layout = Inline { cdotsOpen = "\\cdots\\\n       ", cdotsClose = "" }
                    }
                )
      , condition = After "\\quad" "(n\\geq 2)"
      , lean =
            Generated
                { name = "lams"
                , params = [ { name = "e", ref = Plain Exp } ]
                , result = Exp
                , seqParam = Just { name = "ps", items = [ Item AtPat ] }
                , whenEmpty = Nothing
                }
      }
    , { label = "df:negation"
      , block = AtomicExpressions
      , derived = [ Kw "-", M (Plain AtExp) ]
      , equivalent = Template (TParen (TApp (TVarQual "Basics" "negate") (TMeta (Plain AtExp))))
      , condition = NoCondition
      , lean =
            Generated
                { name = "neg"
                , params = [ { name = "a", ref = Plain AtExp } ]
                , result = AtExp
                , seqParam = Nothing
                , whenEmpty = Nothing
                }
      }
    , { label = "df:list"
      , block = AtomicExpressions
      , derived = [ Kw "[", Raw "\\expm_1", Kw ",", Raw "\\ \\cdots", Kw ",", Raw "\\ \\expm_n", Kw "]" ]
      , equivalent =
            Template
                (TParen
                    (TNestRight
                        { item = TUse "df:infix" [ TOpLit "::", TMeta (Item Exp), THole ]
                        , base = TNil
                        , wrapInner = False
                        , showSecond = False
                        , layout = Inline { cdotsOpen = "\\cdots\\ \\kw{::}\\ ", cdotsClose = "" }
                        }
                    )
                )
      , condition = After "\\qquad" "(n\\geq 1)"
      , lean =
            Generated
                { name = "listE"
                , params = []
                , result = Exp
                , seqParam = Just { name = "es", items = [ Item Exp ] }
                , whenEmpty = Just TNil
                }
      }
    , { label = "df:field-accessor"
      , block = AtomicExpressions
      , derived = [ Kw ".", M (Plain Lab) ]
      , equivalent = Template (TParen (TLam (TRecordPat1 (Plain Lab)) (TVarOfLab (Plain Lab))))
      , condition = NoCondition
      , lean =
            Generated
                { name = "accessor"
                , params = [ { name = "l", ref = Plain Lab } ]
                , result = AtExp
                , seqParam = Nothing
                , whenEmpty = Nothing
                }
      }
    , { label = "df:field-selection"
      , block = AtomicExpressions
      , derived = [ M (Plain AtExp), Kw ".", M (Plain Lab) ]
      , equivalent = Template (TParen (TApp (TUse "df:field-accessor" [ TMeta (Plain Lab) ]) (TMeta (Plain AtExp))))
      , condition = NoCondition
      , lean =
            Generated
                { name = "access"
                , params = [ { name = "a", ref = Plain AtExp }, { name = "l", ref = Plain Lab } ]
                , result = AtExp
                , seqParam = Nothing
                , whenEmpty = Nothing
                }
      }
    , { label = "df:list-pattern"
      , block = AtomicPatterns
      , derived = [ Kw "[", Raw "\\pat_1", Kw ",", Raw "\\ \\cdots", Kw ",", Raw "\\ \\pat_n", Kw "]" ]
      , equivalent =
            Template
                (TNestRight
                    { item = TParen (TPatCons (TMeta (Item Pat)) THole)
                    , base = TNil
                    , wrapInner = False
                    , showSecond = True
                    , layout = Inline { cdotsOpen = "\\cdots\\\n       ", cdotsClose = "\\cdots" }
                    }
                )
      , condition = After "\\quad" "(n\\geq 1)"
      , lean =
            Generated
                { name = "listP"
                , params = []
                , result = AtPat
                , seqParam = Just { name = "ps", items = [ Item Pat ] }
                , whenEmpty = Nothing
                }
      }
    , { label = "df:function-binding"
      , block = ValueBindings
      , derived =
            [ Raw "\\begin{array}[t]{@{}l@{}}\n         \\var\\ \\opt{\\kw{:}\\ \\ty}\\ \\atpat_1\\cdots\\atpat_n\\ \\kw{=}\\ \\expm\\\\\n         \\quad\\opt{\\kw{and}\\ \\valbind}\n       \\end{array}" ]
      , equivalent =
            Computed
                [ Raw "\\begin{array}[t]{@{}l@{}}\n         \\var\\ \\opt{\\kw{:}\\ \\ty}\\ \\kw{=}\\\n           \\kw{\\textbackslash}\\atpat_1\\cdots\\atpat_n\\ \\kw{->}\\ \\expm\\\\\n         \\quad\\opt{\\kw{and}\\ \\valbind}\n         \\qquad (n\\geq 1)\n       \\end{array}" ]
      , condition = NoCondition
      , lean = HandWritten "Derived.lean: Def.fn and groupBind"
      }
    , { label = "df:let-grouping"
      , block = Declarations
      , derived = [ Raw "\\kw{let}\\ \\valbind_1\\ \\cdots\\ \\valbind_n\\ \\kw{in}\\ \\expm" ]
      , equivalent =
            Computed
                [ Raw "\\begin{array}[t]{@{}l@{}}\n         \\kw{let}\\ \\dec_1\\ \\kw{in}\\ \\cdots\\ \\kw{let}\\ \\dec_k\\ \\kw{in}\\ \\expm\\\\\n         \\text{(see Section~\\ref{sec:appendix-derived-forms-let})}\n         \\qquad (n\\geq 2)\n       \\end{array}" ]
      , condition = NoCondition
      , lean = HandWritten "Derived.lean: components, groupBind, letDefs"
      }
    , { label = "df:module-grouping"
      , block = TopLevelDeclarations
      , derived = [ Raw "\\topdec_1\\ \\cdots\\ \\topdec_n" ]
      , equivalent =
            Computed
                [ Raw "\\begin{array}[t]{@{}l@{}}\n         \\kw{type}\\ \\datbind\\ \\kw{;}\\\\\n         \\kw{type alias}\\ \\typbind'_1\\ \\kw{;}\\ \\cdots\\\n           \\kw{type alias}\\ \\typbind'_l\\ \\kw{;}\\\\\n         \\topdec'_1\\ \\kw{;}\\ \\cdots\\ \\kw{;}\\ \\topdec'_k\\\\\n         \\text{(see Section~\\ref{sec:appendix-derived-forms-modules})}\n         \\qquad (n\\geq 2)\n       \\end{array}" ]
      , condition = NoCondition
      , lean = HandWritten "Derived.lean: letDefs over a program's defs"
      }
    ]
