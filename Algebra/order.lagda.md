****
[Contents](contents.html)
[Previous](Algebra.introduction.html)
[Next](Algebra.groups.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Introduction](#introduction)
  - [Preorder](#preorder)
  - [Partial Order or Poset](#partial-order-or-poset)
  - [Total Order](#total-order)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Introduction

```agda
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Types.equality using (IsEquivalence; Reflexive; Symmetric; Transitive; Rel; _⇒_)
open import Types.product using (Σ; _,_; _∪_)

module Algebra.order {a ℓ} {A : Set a} (_==_ : Rel A ℓ) where
```

The equivalence relation remains the most basic relation to be built on objects of all kinds. Higher relations which tend to impose further structural constraints on objects thus creating richer objects and their APIs capable of modeling more complex phenomenon (not much unlike how a programming language's [expressiveness](https://en.wikipedia.org/wiki/Expressive_power_(computer_science)) enables one to build more complex programs).

Order is one such higher relation and is fundamental in building a class of structures. There are different kinds of ordered relations each with progressively stricter laws.

| Relation | Reflexivity | Transitivity | Antisymmetry | Total |
| --- | --- | --- | --- | --- |
| Pre-order | :heavy_check_mark: | :heavy_check_mark: | | |
| Partial-order | :heavy_check_mark: | :heavy_check_mark: | :heavy_check_mark: | |
| Total order | :heavy_check_mark: | :heavy_check_mark: | :heavy_check_mark: | :heavy_check_mark: |

## Preorder

Preorders are binary relations (`~ : A → A`) on a set where:

1. `~` is reflexive, i.e. `x ∼ x`
2. `~` is transitive, i.e. `x ∼ y and y ∼ z ⇒ x ∼ z`

Preorders are relations which are reflexive and transitive.

We first define an object that encapsulates all the rules into one record:

```agda
  record IsPreorder (_∼_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    field
      reflexive     : Reflexive _∼_
      trans         : Transitive _∼_
```

## Partial Order or Poset

Partial orders are a subtype of pre-orders where `≤ : A → A`:

1. `≤` is reflexive, i.e. `x ≤ x`
2. `≤` is transitive, i.e. `x ≤ y and y ≤ z ⇒ x ≤ z`
3. `≤` is antisymmetric, i.e. `x ≤ y and y ≤ x ⇒ x = y`

A partial order, or partially ordered set or Poset, is an antisymmetric preorder. In plain words, we require the relation $_≤_$ to be antisymmetric with respect to the underlying equality .

A relation $_≤_$ is anti-symmetric over the underlying equality $_==_$, if for every $x, y$,

$$
x ≤ y , y ≤ x ⟹ x == y
$$

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
```

## Total Order

Total orders are binary relations `≤ : A → A` where:

1. `≤` is reflexive, i.e. `x ≤ x`
2. `≤` is transitive, i.e. `x ≤ y and y ≤ z ⇒ x ≤ z`
3. `≤` is antisymmetric, i.e. `x ≤ y and y ≤ x ⇒ x = y`
4. `≤` is a total relation, i.e. `∀ x and y : x ≤ y or y ≤ x`

Total orders are a further constrained subtype of posets. All pairs of elements contained in a poset need not be comparable. This is exactly what total orders represent. A total order is a total preorder, or the preorder's relation $_≤_$ to be a total function.

A relation $_≤_$ is total if $x ≤ y$ or $y ≤ x$. This relation has to exist between any pair of elements of `A`:

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
