#!/bin/sh
mkdir $1
cp eushield* infthesis.cls ugcheck.sty dissertation.bib agda.sty $1
cp -r fonts $1
for file in *.lagda.tex
do
    agda --latex --latex-dir=$1 $file
done
