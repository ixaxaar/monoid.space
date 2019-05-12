<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Groups and family](#groups-and-family)
- [Equivalence](#equivalence)
- [Implication](#implication)
- [Pre-order](#pre-order)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Groups and family

```agda
module Algebra.order where

open import Types.equality
open import Types.functions
open import Types.typeBasics

open import Algebra.introduction

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
```

# Equivalence

Before we define groups, we have to define the laws of equivalence:

```lauda
record IsEquivalence {a ℓ} {A : Set a} (_==_ : Rel A ℓ) : Set (a ⊔ ℓ) where
  field
    refl  : Reflexive _==_
    sym   : Symmetric _==_
    trans : Transitive _==_

  reflexive : _≡_ ⇒ _≈_
  reflexive ≡-refl = refl
```

# Implication



# Pre-order

```lauda
record Preorder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _∼_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ₁  -- The underlying equality.
    _∼_        : Rel Carrier ℓ₂  -- The relation.
```


