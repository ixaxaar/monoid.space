<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Equivalence](#equivalence)
  - [Respect](#respect)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Equivalence

```agda
module Algebra.equality where

open import Types.equality
open import Types.functions
open import Types.typeBasics

open import Algebra.introduction

open import Level
```

We start our algebraic machinery the definiton for **respect**.

## Respect

```agda
_Respects_ : ∀ {a ℓ₁ ℓ₂} {A : Set a}
        → (A → Set ℓ₁)
        → Rel A ℓ₂
        → Set _
P Respects _∼_ = ∀ {x y} → x ∼ y → P x → P y

_Respectsʳ_ : ∀ {a ℓ₁ ℓ₂} {A : Set a}
        → Rel A ℓ₁
        → Rel A ℓ₂
        → Set _
P Respectsʳ _∼_ = ∀ {x} → (P x) Respects _∼_

_Respectsˡ_ : ∀ {a ℓ₁ ℓ₂} {A : Set a}
        → Rel A ℓ₁
        → Rel A ℓ₂
        → Set _
P Respectsˡ _∼_ = ∀ {y} → (flip P y) Respects _∼_

_Respects₂_ : ∀ {a ℓ₁ ℓ₂} {A : Set a}
        → Rel A ℓ₁
        → Rel A ℓ₂
        → Set _
P Respects₂ _∼_ = (P Respectsʳ _∼_) × (P Respectsˡ _∼_)
```
