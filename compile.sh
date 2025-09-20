#!/usr/bin/env bash

set -e
set -o pipefail

declare -a files=(
  "contents"

  "Lean/setup"
  "Lean/naming"
  "Lean/types"
  "Lean/functions"
  "Lean/algorithms"
  "Lean/other"
  "Lean/debugging"

  "Types/introduction"
  "Types/universe"
  "Types/relations"
  "Types/equality"
  "Types/operations"
  "Types/product"
  "Types/functions"
  "Types/identity"

  "Proofs/introduction"
  "Proofs/tactics"

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
  "Category/naturalTransformation"
  "Category/yoneda"

  "AlgTopos/introduction"

  "HoTT/introduction"
  "HoTT/homotopy"

  "AppliedTypes/introduction"
  "AppliedTypes/godels_t"
  "AppliedTypes/system_f"
  "AppliedTypes/bitcoin"
  "AppliedTypes/verified_programming"
)

rm -rf build html tmp .lean
mkdir html .lean

cd src || exit 1

for i in "${files[@]}"; do
  echo "Updating TOC for ${i}.md"
  doctoc "${i}.md" --title "**Table of Contents**"
  
  echo "Generating HTML for ${i}.md"
  pandoc -s --mathjax --css=../css/agda.css --from=markdown+smart --to=html --metadata pagetitle="${i}" --columns=120 -o "../html/${i/\//.}.html" "${i}.md"
done

cd .. || exit 1

# Copy resources
cp -pr ./artwork ./html/
cp -pr ./css ./html
