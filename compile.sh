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
  "Types/operations"
  "Types/functions"
  "Types/functions2"
  "Types/product"

  "Types/proofsAsData"
  "Types/variations"
  "Types/patterns"
  "Types/equational"
  "Types/equational2"

  "AppliedTypes/introduction"
  "AppliedTypes/godels_t"
  "AppliedTypes/system_f"
  "AppliedTypes/bitcoin"
  "AppliedTypes/verified_programming"

  "Logic/introduction"
  "Logic/logicBasics"
  "Logic/equality"
  "Logic/laws"
  "Logic/decidability"

  "HoTT/introduction"
  "HoTT/identity"

  "Algebra/introduction"
  "Algebra/order"
  "Algebra/groups"
  "Algebra/groups2"
  "Algebra/morphisms"
  "Algebra/rings"
  "Algebra/fields"
  "Algebra/numbers"
)

stack build
rm -rf build html tmp
mkdir html

# compile
agda -i . --compile --without-K --no-main --compile-dir=./build contents.lagda.md

for i in "${files[@]}"
do
  if [[ $i != "contents" ]]; then
    # generate TOC
    doctoc --github --title '****' "${i}.lagda.md" &> /dev/null
  fi

  # remove doctoc's text
  sed -i "s/\*generated with \[DocToc\](https:\/\/github.com\/thlorenz\/doctoc)\*//g" "${i}.lagda.md"

  echo "Generating HTML for " "${i}.lagda.md"
  pandoc -s --mathjax --css=../css/agda.css --from=markdown+smart --to=html --metadata pagetitle="${i}" --columns=120 -o ./html/${${i/\.\//}/\//\.}.html "${i}.lagda.md"

done

# copy resources
cp -pr ./artwork/*.png ./html/

find -name "*.agdai" | xargs rm -rf

cp -pr ./css  ./html
