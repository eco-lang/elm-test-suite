# Value Framework

What each part of the book must deliver. Before drafting a chapter, the agent
and the human lock which values the chapter targets and what would show each
one has been delivered. The audit checks the locked targets.

## Value Types

| Value | Meaning | Delivered When |
|-------|---------|----------------|
| PRECISE | The text decrees exactly which sentences hold, with no gaps | Every production has a rule; every object and operation is defined; no rule needs prose to be read |
| FAITHFUL | The definition matches the language as ruled in the ambiguity log | Every behaviour in the survey for this chapter is accounted for; every ruling is honoured or flagged |
| ECONOMICAL | The fewest rules and objects that achieve PRECISE | Options merge near-duplicate rules; derived forms carry everything that can be translated; no object is defined and then unused |
| TRACTABLE | The objects have the properties needed for the rules to make sense | Each property the rules rely on is stated (definition-style O7) |
| ILLUMINATING | A careful reader can see why each non-obvious rule is the way it is | Each side condition and each surprising absence has a Comment |

## Defaults by Chapter Kind

| Chapter | Required | Usually Also |
|---------|----------|--------------|
| Syntax | PRECISE, FAITHFUL | ECONOMICAL |
| Static semantics | PRECISE, FAITHFUL, TRACTABLE | ILLUMINATING, ECONOMICAL |
| Dynamic semantics | PRECISE, FAITHFUL | ILLUMINATING, ECONOMICAL |
| Derived forms appendix | PRECISE, ECONOMICAL | FAITHFUL |
| Initial basis appendices | PRECISE, FAITHFUL | |
| Preface and introduction | ILLUMINATING | |

## Locking Targets

At the chapter's first checkpoint, write a short value brief as a LaTeX
comment block at the top of the chapter's `.tex` file:

```
% Values: PRECISE, FAITHFUL, TRACTABLE, ILLUMINATING
% Evidence planned:
% - PRECISE: rules for all 14 bare productions of Exp and Dec
% - TRACTABLE: state the property that tynames E is within T is preserved
% - ILLUMINATING: comments for the let side condition and raise
```
