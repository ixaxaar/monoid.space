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
   doctoc "${i}.lagda.md"
   echo """
   [Contents](./contents.html)
   """ >> "${i}.ladga.md"
   sed -i "s/\*generated with \[DocToc\](https:\/\/github.com\/thlorenz\/doctoc)\*//g" "${i}.lagda.md"
   agda --compile --no-main --html --html-dir=./tmp --css=./css --compile-dir=./build "${i}.lagda.md"
   echo "Generating HTML for " "${i}.lagda.md"
   pandoc -s -S --css=../css/agda.css --from=markdown_github --to=html --columns=80 -o ./html/"${i/\//\.}.html" "${i}.lagda.md"
   git checkout "${i}.ladga.md"
done

rm -rf tmp
