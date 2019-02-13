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


for i in "${files[@]}"
do
   echo "Compiling" "${i}.ladga.md"
   agda --compile --compile-dir=./build "${i}.lagda.md"
done

