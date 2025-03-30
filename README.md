# System F in Agda via Pitts

By Charlotte Ausel.

This is a repository to hold the code for my final project submitted as part of my Computer Science
and Mathematics degree at the University of Edinburgh. The Agda code can be found in the root
directory, and the LaTeX source file in the `latex` directory.

## Compilation instructions

### Agda

This was tested to work with Agda 2.7.0 and the Agda Standard Library 2.1. Simply run the
`dissertation.agda` or any other Agda file in your favourite Agda editor, such as Emacs.

### LaTeX

All the LaTeX files can be found in the `./latex` directory. The LaTeX file was tested to work with
XeLaTeX 3.141592653-2.6-0.999997 (TeX Live 2026/dev/Arch Linux) (using the Arch Linux
`texlive-xetex` package 2025.2-1). To compile the LaTeX source file, you will need to run XeTeX with
the `--shell-escape` option, as this project uses the Minted package which requires it. While
`latexmk` is not required, the instructions will assume you have it available.

1. Change directory to `./latex`.
2. Choose a temporary directory to compile the LaTeX and PDF files to. We will refer to this as
   `$TMP`.
3. Run `./agda_build.sh $TMP` to build the literate Agda LaTeX files. The script will exit with code
   0 if it's successful. The script is written for a Linux target, but should be relatively easy to
   modify for other operating systems by inspecting its source code.
4. Run `latexmk -xelatex -shell-escape -cd $TMP/dissertation.tex` (I'd recommend the `-quiet` option
   too).
5. The compiled document will be in `$TMP/dissertation.pdf`.
