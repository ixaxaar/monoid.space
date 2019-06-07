#!/usr/bin/env bash

declare -a files=(
  "contents"

  "Lang/setup"
  "Lang/intro"
  "Lang/dataStructures"
  "Lang/functions"
  "Lang/syntaxQuirks"
  "Lang/other"
  "Lang/debugging"

  "Types/introduction"
  "Types/universe"
  "Types/relations"
  "Types/equality"
  "Types/functions"
  "Types/product"
  "Types/proofsAsData"
  "Types/variations"

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
  "Algebra/groups2"
  "Algebra/groupProperties"
)

rm -rf build html tmp
mkdir html

 # compile
 agda -i . --compile --without-K --no-main --compile-dir=./build contents.lagda.md

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
   pandoc -s --mathjax --css=../css/agda.css --from=markdown+smart --to=html --columns=120 -o ./html/"${i/\//\.}.html" "${i}.lagda.md"

done

# copy resources
cp -pr ./artwork/*.png ./html/

rm -rf tmp
find -name "*.agdai" | xargs rm -rf

cp -pr ./css  ./html
