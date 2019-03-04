<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Algebraic structures](#algebraic-structures)
    - [Operations](#operations)
  - [Associativity](#associativity)
  - [Commutativity](#commutativity)
  - [Identity](#identity)
  - [Elimination](#elimination)
  - [Distributive](#distributive)
  - [Absorptive](#absorptive)
  - [Cancellative](#cancellative)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Algebraic structures

```agda
open import Types.relations using (Rel; Equivalence)

open import Types.typeBasics using (_×_; _,_; _∪_; inj₁; inj₂)

module Algebra.introduction {A : Set} (eq : Equivalence A) where

  module Eq₁ = Equivalence eq
  open Eq₁
```

Here we start to dive into more complex structures - both structured data and maps (function families). Most of these structures are constructed by picking and choosing certain underlying laws or properties of these function families. We first start with building such laws. Many of these laws are similar to the ones of logic that we derived in a [previous part](./Logic.laws.html/#operations).

### Operations

A binary operation `★ A` can be defined as:

```agda
  ★_ : Set → Set
  ★ A = A → A → A
```

## Associativity

![associative](associative.png)

```agda
  Associative : ★ A → Set _
  Associative _∙_ = ∀ x y z → ((x ∙ y) ∙ z) == (x ∙ (y ∙ z))
```

## Commutativity

![commutative](commutative.png)

```agda
  Commutative : ★ A → Set _
  Commutative _∙_ = ∀ x y → (x ∙ y) == (y ∙ x)
```

## Identity

![identity](identity.png)

```agda
  LeftIdentity : A → ★ A → Set _
  LeftIdentity e _∙_ = ∀ x → (e ∙ x) == x

  RightIdentity : A → ★ A → Set _
  RightIdentity e _∙_ = ∀ x → (x ∙ e) == x

  Identity : A → ★ A → Set _
  Identity e ∙ = LeftIdentity e ∙ × RightIdentity e ∙
```

## Elimination

![elimination](elimination.png)

```agda
  LeftZero : A → ★ A → Set _
  LeftZero z _∙_ = ∀ x → (z ∙ x) == z

  RightZero : A → ★ A → Set _
  RightZero z _∙_ = ∀ x → (x ∙ z) == z

  Zero : A → ★ A → Set _
  Zero z ∙ = LeftZero z ∙ × RightZero z ∙
```

## Distributive

![distributive](distributive.png)

```agda
  _DistributesOverˡ_ : ★ A → ★ A → Set _
  _*_ DistributesOverˡ _+_ =
    ∀ x y z → (x * (y + z)) == ((x * y) + (x * z))

  _DistributesOverʳ_ : ★ A → ★ A → Set _
  _*_ DistributesOverʳ _+_ =
    ∀ x y z → ((y + z) * x) == ((y * x) + (z * x))

  _DistributesOver_ : ★ A → ★ A → Set _
  * DistributesOver + = (* DistributesOverˡ +) × (* DistributesOverʳ +)
```

<!-- ## Selective

```haskell
  Selective : ★ A → Set _
  Selective _∙_ = ∀ x y → (x ∙ y) == x ∪ (x ∙ y) == y
```
 -->
## Absorptive

![absorption](absorption.png)

```agda
  _Absorbs_ : ★ A → ★ A → Set _
  _∙_ Absorbs _∘_ = ∀ x y → (x ∙ (x ∘ y)) == x

  Absorptive : ★ A → ★ A → Set _
  Absorptive ∙ ∘ = (∙ Absorbs ∘) × (∘ Absorbs ∙)
```

## Cancellative

![cancellation](cancellation.png)

```agda
  LeftCancellative : ★ A → Set _
  LeftCancellative _•_ = ∀ x {y z} → (x • y) == (x • z) → y == z

  RightCancellative : ★ A → Set _
  RightCancellative _•_ = ∀ {x} y z → (y • x) == (z • x) → y == z

  Cancellative : ★ A → Set _
  Cancellative _•_ = LeftCancellative _•_ × RightCancellative _•_
```

****
[Back to Contents](./contents.html)
