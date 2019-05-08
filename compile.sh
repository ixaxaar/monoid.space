#!/usr/bin/env bash

declare -a files=(
  "intro"
  "contents"

  "Lang/setup"
  "Lang/languageIntro"
  "Lang/dataStructures"
  "Lang/functions"
  "Lang/proofsAsData"
  "Lang/syntaxQuirks"
  "Lang/other"
  "Lang/debugging"

  "Types/introduction"
  "Types/universe"
  "Types/relations"
  "Types/equality"
  "Types/functions"
  "Types/typeBasics"

  "Logic/introduction"
  "Logic/logicBasics"
  "Logic/equality"
  "Logic/laws"
  "Logic/decidability"

  "HoTT/introduction"
  "HoTT/identity"

  "Algebra/introduction"
  "Algebra/operations"
  "Algebra/equational"
  "Algebra/order"
  "Algebra/groups"
  "Algebra/structures"
  "Algebra/groupProperties"
)

rm -rf build html tmp
mkdir html

 # compile
 agda -i . --compile --no-main --compile-dir=./build contents.lagda.md

for i in "${files[@]}"
do
   echo "Reformatting" "${i}.ladga.md"

   # generate TOC
   doctoc --github --title '****' "${i}.lagda.md"

   # remove doctoc's text
   sed -i "s/\*generated with \[DocToc\](https:\/\/github.com\/thlorenz\/doctoc)\*//g" "${i}.lagda.md"

   # Push ref to start
   # echo """
   # [Contents](./contents.html)
   # """ >> "${i}.ladga.md"

   echo "Generating HTML for " "${i}.lagda.md"
   pandoc -s -S --css=../css/agda.css --from=markdown --to=html --columns=120 -o ./html/"${i/\//\.}.html" "${i}.lagda.md"

done

# copy resources
find . -name "*.png" | xargs cp -pr -t ./html

rm -rf tmp
find -name "*.agdai" | xargs rm -rf

cp -pr ./css ./html
cp -pr ./space.png ./html
