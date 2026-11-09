# TeX Live Setup

TeX Live is the LaTeX distribution that builds the book. `latexmk` runs the
LaTeX engine as many times as needed. Stages 03 to 05 also use the engine for
chapter previews.

## Install

Debian or Ubuntu:

```
sudo apt install texlive-latex-base texlive-latex-recommended \
  texlive-latex-extra texlive-fonts-recommended latexmk
```

Add `texlive-xetex` or `texlive-luatex` if run-config names XeLaTeX or
LuaLaTeX.

macOS: install MacTeX from https://tug.org/mactex/ (includes everything).

## Packages the Workspace Needs

`defn.sty` needs only `iftex`, `amsmath`, `amssymb`, `array` and, under
pdfLaTeX, `fontenc`. The master document adds `microtype` and `hyperref`. All
are in the packages above.

## Verify

```
latexmk -v
pdflatex --version        # or the engine named in run-config
kpsewhich amsmath.sty microtype.sty hyperref.sty iftex.sty
```

Each command prints a version or a path. A missing path means a missing
package: install `texlive-latex-extra`.

## How the Workspace Uses It

- The writing stages (03 to 05) compile each chapter alone with
  `latex/chapter-preview.tex` (see `latex/latex-conventions.md` "Preview").
- The typeset stage (08) builds the whole book with `latexmk` in its own
  build folder.
