#!/usr/bin/env bash

declare -a files=(
  "contents"

  "Lang/setup"
  "Lang/intro"
  "Lang/naming"
  "Lang/dataStructures"
  "Lang/functions"
  "Lang/syntaxQuirks"
  "Lang/other"
  "Lang/debugging"

  "Types/introduction"
  "Types/universe"
  "Types/relations"
  "Types/equality"
  "Types/operations"
  "Types/functions"
  "Types/functions2"
  "Types/product"

  "Types/proofsAsData"
  "Types/variations"
  "Types/patterns"
  "Types/equational"
  "Types/equational2"

  "Logic/introduction"
  "Logic/logicBasics"
  "Logic/equality"
  "Logic/laws"
  "Logic/decidability"

  "Algebra/introduction"
  "Algebra/sets"
  "Algebra/order"
  "Algebra/groups"
  "Algebra/groups2"
  "Algebra/groupMorphisms"
  "Algebra/rings"
  "Algebra/rings2"
  "Algebra/ringMorphisms"
  "Algebra/fields"
  "Algebra/fields2"
  "Algebra/fieldMorphisms"
  "Algebra/numbers"

  "Category/introduction"
  "Category/category"
  "Category/morphisms"
  "Category/functors"
  "Categry/naturalTransformation"

  "AlgTopos/introduction"

  "HoTT/introduction"
  "HoTT/homotopy"

  "AppliedTypes/introduction"
  "AppliedTypes/godels_t"
  "AppliedTypes/system_f"
  "AppliedTypes/bitcoin"
  "AppliedTypes/verified_programming"
)

stack build
rm -rf build html tmp
mkdir html

cd src

# compile
agda -i . --compile --without-K --no-main --compile-dir=../build contents.lagda.md

for i in "${files[@]}"
do
  if [[ $i != "contents" ]]; then
    # generate TOC
    doctoc --github --title '****' "${i}.lagda.md" &> /dev/null
  fi

  # remove doctoc's text
  sed -i "s/\*generated with \[DocToc\](https:\/\/github.com\/thlorenz\/doctoc)\*//g" "${i}.lagda.md"

  echo "Generating HTML for " "${i}.lagda.md"
  pandoc -s --mathjax --css=../css/agda.css --from=markdown+smart --to=html --metadata pagetitle="${i}" --columns=120 -o ../html/${${i/\.\//}/\//\.}.html "${i}.lagda.md"

done

cd ..

# copy resources
cp -pr ./artwork ./html/

find -name "*.agdai" | xargs rm -rf

cp -pr ./css  ./html
