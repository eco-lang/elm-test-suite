# Notation Format

The notation registry is the single home of every name and symbol in the book.
`macros.sty` is generated from it. Chapters use only registered notation,
through its macro.

## Registry

```
# Notation Registry: <Title>

## Conventions
- Decorated metavariables (primes, subscripts) range over the same class.
- Any other book-wide notational conventions, one line each.

## Syntactic Classes
| Class | Metavariable | Macro | Description | Level |
| VId | vid | \vid | value identifiers | Core |
| Exp | exp | \expm (see "Macro Names") | expressions | Core |

## Semantic Classes
| Class | Metavariable | Macro (class) | Macro (var) | Definition | Phase | Level |
| TyVar | alpha | \TyVar | \tyvarsym | simple | static | Core |
| TypeScheme | sigma | \TypeScheme | \tsch | union over k of TyVar^k x Type | static | Core |

## Operations
| Operation | Written | Macro | Defined In | Meaning (one line) |
| modification | A + B | (plain +) | static-core | right map overrides left |
| closure | Clos_C(tau) | \Clos | static-core | generalise over free variables not in C |

## Judgment Forms
| Phase | Level | Phrase Class | Form | Macro | Pronounced |
| static | Core | Exp | C |- exp => tau | \jexp | exp elaborates to tau in C |
| dynamic | Core | Exp | E |- exp => v/p | \djexp | exp evaluates to v or p in E |

## Special Symbols
| Symbol | Macro | Meaning |
```

## Rules for the Registry

1. **One row per name.** A metavariable letter is used by one class only
   within a phase. If the static and dynamic semantics both need `v`, they
   must mean the same class or one is renamed.
2. **Syntactic before semantic.** Syntactic metavariables are italic words
   (`exp`), set with `\mv`. Semantic metavariables are single Greek or Latin
   letters where the exemplar's practice allows (`tau`, `E`, `C`).
3. **Judgment forms name every component.** The form shows the context, the
   phrase metavariable and the result, with the same arrow for every class in a
   phase.
4. **Defined In** names the chapter where the operation is first defined, which
   must come before its first use in Chapter Order.
5. **No synonyms.** If two names would mean the same thing, keep one.

## Macro Names

- Classes: the class name as a command (`\TyVar`, `\TypeScheme`), expanding
  to `\cls{...}`.
- Syntactic metavariables: the metavariable as a command (`\vid`, `\atexp`),
  expanding to `\mv{...}`. Where the name is already a LaTeX command
  (`\exp`, `\dim`, `\det`), append `m`: `\expm`.
- Judgments: `\j<class>` for static, `\dj<class>` for dynamic, with the
  context and result as arguments: `\jexp{C}{\expm}{\tau}`.
- Never redefine a LaTeX kernel, amsmath or `defn.sty` command. Use
  `\newcommand`, never `\renewcommand` or `\def`, so a clash is an error.

## Generating macros.sty

Write the package in registry order, one block per registry section, each
macro on its own line with the registry row as a trailing comment:

```
\NeedsTeXFormat{LaTeX2e}
\ProvidesPackage{macros}[<date> Notation for <Title>, generated from notation.md]
\RequirePackage{defn}
% Syntactic classes
\newcommand{\vid}{\mv{vid}}            % VId: value identifiers
% Semantic classes
\newcommand{\TyVar}{\cls{TyVar}}       % simple, static Core
% Judgment forms
\newcommand{\jexp}[3]{#1 \vdash #2 \Rightarrow #3}  % Exp, static Core
\endinput
```

Prove it loads by compiling `../../shared/latex/chapter-preview.tex` with an
empty chapter file. Regenerate the whole file whenever the registry changes;
never edit it by hand.
