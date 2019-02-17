#!/usr/bin/env bash

declare -a files=(
  "intro"
  "contents"

  "Lang/setup"
  "Lang/languageIntro"
  "Lang/dataStructures"
  "Lang/functions"
  "Lang/proofsAsData"
  "Lang/other"

  "Types/introduction"
  "Types/relations"
  "Types/equality"
  "Types/typeBasics"
  "Types/universe"
)

rm -rf build html tmp
mkdir html

for i in "${files[@]}"
do
   echo "Compiling" "${i}.ladga.md"

   # generate TOC
   doctoc --github --title '****' "${i}.lagda.md"

   # remove doctoc's text
   sed -i "s/\*generated with \[DocToc\](https:\/\/github.com\/thlorenz\/doctoc)\*//g" "${i}.lagda.md"

   # Push ref to start
   # echo """
   # [Contents](./contents.html)
   # """ >> "${i}.ladga.md"

   # compile
   agda -i . --compile --no-main --compile-dir=./build "${i}.lagda.md"

   echo "Generating HTML for " "${i}.lagda.md"
   pandoc -s -S --css=../css/agda.css --from=markdown --to=html --columns=80 -o ./html/"${i/\//\.}.html" "${i}.lagda.md"

done

# copy resources
find . -name "*.png" | xargs cp -pr -t ./html

rm -rf tmp
