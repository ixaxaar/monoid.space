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

open import Types.typeBasics using (Σ; _,_)

open import Types.relations using (Rel; Equivalence; Reflexive; Symmetric; Transitive)

open import Algebra.introduction

open import Level
```

# Equivalence

Before we define groups, we have to define the laws of equivalence:

```agda
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

```agda
record Preorder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _∼_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ₁  -- The underlying equality.
    _∼_        : Rel Carrier ℓ₂  -- The relation.
```


