# System F in Agda via Pitts

By Charlotte Ausel.

This is a repository to hold the code for my final project submitted as part of my Computer Science
and Mathematics degree at the University of Edinburgh. The Agda code can be found in the root
directory, and the LaTeX source file in the `latex` directory.

# Compilation instructions

This was tested to work with Agda 2.7.0, the Agda Standard Library 2.1, and XeTeX
3.141592653-2.6-0.999997 (TeX Live 2025/Arch Linux 2024.1-1). Simply run the `dissertation.agda` or
any other Agda file in your favourite Agda editor, such as Emacs. To compile the LaTeX source file,
you will need to run XeTeX with the `--shell-escape` option, as this project uses the Minted package
which requires it.