#!/usr/bin/env bash

declare -a files=(
  "intro"
  "contents"

  "Lang/setup"
  "Lang/languageIntro"
  "Lang/dataStructures"
  "Lang/functions"
  "Lang/proofsAsData"
)

rm -rf build html tmp
mkdir html

for i in "${files[@]}"
do
   echo "Compiling" "${i}.ladga.md"
   agda --compile --no-main --html --html-dir=./tmp --css=./css --compile-dir=./build "${i}.lagda.md"
   echo "Generating HTML for " "${i/\//\.}.html"
   pandoc -o ./html/"${i/\//\.}.html" ./tmp/"${i/\//\.}.html"
done

rm -rf tmp
