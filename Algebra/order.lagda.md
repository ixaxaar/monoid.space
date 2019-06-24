****
[Contents](contents.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Introduction](#introduction)
  - [Pre-order](#pre-order)
  - [Partial Order or Poset](#partial-order-or-poset)
  - [Total Order](#total-order)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Introduction

```agda
module Algebra.order where

open import Types.equality using (IsEquivalence; Reflexive; Symmetric; Transitive; Rel; _⇒_)
open import Types.product using (Σ; _,_; _∪_)
open import Types.operations

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
```

The equivalence relation remains the most basic relation to be built on objects of all kinds. Higher relations which tend to impose further structural constraints on objects thus creating richer objects and their APIs capable of modeling more complex phenomenon (not much unlike how a programming language's [expressiveness](https://en.wikipedia.org/wiki/Expressive_power_(computer_science)) enables one to build more complex programs).

Order is one such higher relation and is fundamental in building a class of structures. There are different kinds of ordered objects each with progressively stricter laws.

## Pre-order

Preorders are relations which are reflexive and transitive. The property of symmetry is left out, and in such a way, preorders are even more general (less strict) than equivalences. We define a pre-order set of objects with an underlying notion of equality `_≈_`.

We first define an object that encapsulates all the rules into one record:

```lauda
record IsPreorder {a ℓ₁ ℓ₂} {A : Set a}
                  (_≈_ : Rel A ℓ₁) -- The underlying equality.
                  (_∼_ : Rel A ℓ₂) -- The relation.
                  : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isEquivalence : IsEquivalence _≈_
    -- Reflexivity is expressed in terms of an underlying equality,
    -- reflexivity of the underlying equality implies reflexivity of the relation:
    reflexive     : _≈_ ⇒ _∼_
    trans         : Transitive _∼_

  module Eq = IsEquivalence isEquivalence

  refl : Reflexive _∼_
  refl = reflexive Eq.rfl

  -- we ensure the relation _∼_ respects the underlying equality:
  -- we cannot use commutativity, hence we use the _Respects₂_ version here.
  ∼-respˡ-≈ : _∼_ Respectsˡ _≈_
  ∼-respˡ-≈ x≈y x∼z = trans (reflexive (Eq.sym x≈y)) x∼z

  -- ∼-respʳ-≈ : _∼_ Respectsʳ _≈_
  -- ∼-respʳ-≈ x≈y z∼x = trans z∼x (reflexive x≈y)

  -- ∼-resp-≈ : _∼_ Respects₂ _≈_
  -- ∼-resp-≈ = ∼-respʳ-≈ , ∼-respˡ-≈
```

Finally we define the actual object:

```lauda
record Preorder c ℓ₁ ℓ₂ : Set (lsuc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _∼_
  field
    Data       : Set c
    _≈_        : Rel Data ℓ₁  -- The underlying equality.
    _∼_        : Rel Data ℓ₂  -- The relation.
    isPreorder : IsPreorder _≈_ _∼_

  open IsPreorder isPreorder public
```

## Partial Order or Poset

A partial order, or partially ordered set or Poset, is an antisymmetric preorder. In plain words, we require the relation $_≤_$ to be antisymmetric.

A relation $_≤_$ is anti-symmetric over the underlying equality $_≈_$, if for every $x, y$,

$x ≤ y , y ≤ x ⟹ x ≈ y$

```lauda
Antisymmetric : ∀ {a ℓ₁ ℓ₂} {A : Set a} → Rel A ℓ₁ → Rel A ℓ₂ → Set _
Antisymmetric _≈_ _≤_ = ∀ {x y} → x ≤ y → y ≤ x → x ≈ y
```

We can now define partially ordered sets:

```lauda
record IsPartialOrder {a ℓ₁ ℓ₂} {A : Set a}
                      (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) :
                      Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPreorder : IsPreorder _≈_ _≤_
    antisym    : Antisymmetric _≈_ _≤_

  open IsPreorder isPreorder public
    renaming
    ( ∼-respˡ-≈ to ≤-respˡ-≈
    ; ∼-respʳ-≈ to ≤-respʳ-≈
    ; ∼-resp-≈  to ≤-resp-≈
    )
```

```lauda
record Poset c ℓ₁ ℓ₂ : Set (lsuc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≤_
  field
    Data           : Set c
    _≈_            : Rel Data ℓ₁
    _≤_            : Rel Data ℓ₂
    isPartialOrder : IsPartialOrder _≈_ _≤_

  open IsPartialOrder isPartialOrder public

  preorder : Preorder c ℓ₁ ℓ₂
  preorder = record { isPreorder = isPreorder }
```

## Total Order

A total order is a total preorder, or the preorder's relation $_≤_$ to be a total function.

A relation $_≤_$ is total if $x ≤ y or y ≤ x$. There is no third possibility.

```lauda
Total : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Total _∼_ = ∀ x y → (x ∼ y) ∪ (y ∼ x)
```

We can now define total orders:

```lauda
record IsTotalOrder {a ℓ₁ ℓ₂} {A : Set a}
                    (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) :
                    Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    total          : Total _≤_

  open IsPartialOrder isPartialOrder public
```

```lauda
record TotalOrder c ℓ₁ ℓ₂ : Set (lsuc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≤_
  field
    Data         : Set c
    _≈_          : Rel Data ℓ₁
    _≤_          : Rel Data ℓ₂
    isTotalOrder : IsTotalOrder _≈_ _≤_

  open IsTotalOrder isTotalOrder public

  poset : Poset c ℓ₁ ℓ₂
  poset = record { isPartialOrder = isPartialOrder }

  open Poset poset public using (preorder)
```


****
[Groups and family](./Algebra.groups.html)
