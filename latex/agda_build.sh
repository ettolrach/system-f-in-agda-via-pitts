#!/bin/sh

# Make the temporary directory if it doesn't exist yet.
mkdir -p $1
# Copy files required to compile the LaTeX document.
cp eushield* infthesis.cls ugcheck.sty dissertation.bib agda.sty $1
cp -r fonts $1

# We only want to compile .lagda.tex files.
for file in *.lagda.tex
do
    # Compile each of them and set the output directory to the argument.
    # If any of the files failed, exit the script immediately.
    agda --latex --latex-dir=$1 $file || exit 1
done
