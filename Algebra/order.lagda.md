****
[Contents](contents.html)
[Previous](Algebra.introduction.html)
[Next](Algebra.groups.html)

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
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Types.equality using (IsEquivalence; Reflexive; Symmetric; Transitive; Rel; _⇒_)
open import Types.product using (Σ; _,_; _∪_)

module Algebra.order {a ℓ} {A : Set a} (_==_ : Rel A ℓ) where
  open import Types.operations (_==_)
```

The equivalence relation remains the most basic relation to be built on objects of all kinds. Higher relations which tend to impose further structural constraints on objects thus creating richer objects and their APIs capable of modeling more complex phenomenon (not much unlike how a programming language's [expressiveness](https://en.wikipedia.org/wiki/Expressive_power_(computer_science)) enables one to build more complex programs).

Order is one such higher relation and is fundamental in building a class of structures. There are different kinds of ordered objects each with progressively stricter laws.

## Pre-order

Preorders are relations which are reflexive and transitive. The property of symmetry is left out, and in such a way, preorders are even more general (less strict) than equivalences. We define a pre-order set of objects with an underlying notion of equality `_==_`.

We first define an object that encapsulates all the rules into one record:

```agda
  record IsPreorder (_∼_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    field
      isEquivalence : IsEquivalence _==_
      -- Reflexivity is expressed in terms of an underlying equality,
      -- reflexivity of the underlying equality implies reflexivity of the relation:
      reflexive     : _==_ ⇒ _∼_
      trans         : Transitive _∼_

    module Eq = IsEquivalence isEquivalence

    refl : Reflexive _∼_
    refl = reflexive Eq.rfl

    -- we ensure the relation _∼_ respects the underlying equality:
    -- we cannot use commutativity, hence we use the _Respects₂_ version here.
    ∼-respˡ-== : _∼_ Respectsˡ _==_
    ∼-respˡ-== x==y x∼z = trans (reflexive (Eq.sym x==y)) x∼z

    ∼-respʳ-== : _∼_ Respectsʳ _==_
    ∼-respʳ-== x==y z∼x = trans z∼x (reflexive x==y)

    ∼-resp-== : _∼_ Respects₂ _==_
    ∼-resp-== = ∼-respʳ-== , ∼-respˡ-==
```

## Partial Order or Poset

A partial order, or partially ordered set or Poset, is an antisymmetric preorder. In plain words, we require the relation $ _≤_ $ to be antisymmetric.

A relation $ _≤_ $ is anti-symmetric over the underlying equality $ _==_ $, if for every $ x, y $,

$ x ≤ y , y ≤ x ⟹ x == y $

```agda
  Antisymmetric : Rel A ℓ → Rel A ℓ → Set _
  Antisymmetric _==_ _≤_ = ∀ {x y} → x ≤ y → y ≤ x → x == y
```

We can now define partially ordered sets:

```agda
  record IsPartialOrder (_≤_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    field
      isPreorder : IsPreorder _≤_
      antisym    : Antisymmetric _==_ _≤_

    open IsPreorder isPreorder public
      renaming
      ( ∼-respˡ-== to ≤-respˡ-==
      ; ∼-respʳ-== to ≤-respʳ-==
      ; ∼-resp-==  to ≤-resp-==
      )
```

## Total Order

A total order is a total preorder, or the preorder's relation $ _≤_ $ to be a total function.

A relation $ _≤_ $ is total if $ x ≤ y or y ≤ x $. There is no third possibility.

```agda
  Total : {A : Set a} → Rel A ℓ → Set _
  Total _∼_ = ∀ x y → (x ∼ y) ∪ (y ∼ x)
```

We can now define total orders:

```agda
  record IsTotalOrder (_≤_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    field
      isPartialOrder : IsPartialOrder _≤_
      total          : Total _≤_

    open IsPartialOrder isPartialOrder public
```


****
[Groups and family](./Algebra.groups.html)
