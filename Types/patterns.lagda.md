****
[Contents](contents.html)
[Previous](Types.variations.html)
[Next](Types.equational.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Rules of introduction of types](#rules-of-introduction-of-types)
  - [Formation](#formation)
  - [Constructor / Introduction](#constructor--introduction)
  - [Elimination](#elimination)
  - [Computation](#computation)
  - [Uniqueness principle](#uniqueness-principle)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Rules of introduction of types

```agda
module Types.patterns where

open import Lang.dataStructures using (List; _::_; [])
open import Types.product using (Σ; _,_; fst; snd; _∪_; inj₁; inj₂)
```

- **Formation**: how to construct new types of this kind
- **Constructor / Introduction**: how to construct new objects of this type
- **Elimination**: how to use elements of this type
- **Computation**: how eliminator acts on the constructor
- **Uniquness principle**: how are maps related to the type unique

## Formation

We start with describing what are the rules to follow when creating an instance of the type being introduced. It is a "type-constructor-level" law.

For example we introduce natural numbers like:

```agda
data Nat : Set where
  zero : Nat
  succ : Nat → Nat
```

Functions' from `A → B` have formation rules of the types `A` and `B` to exist.
Similarly, products `(A × B)` depend upon the existence of types `A` and `B` and so do co-product types `A ∪ B`.

## Constructor / Introduction

We then proceed to define how an element of the new type could be constructed. For natural numbers, `zero` and `succ` are the constructors:

```agda
one = succ zero
two = succ one
three = succ two
```

Function types can be described by their implementation using lambda abstraction:

```math
f : A → B ≡ λ A . B
```

Products have the constructor `,` to create product types, so do coproducts have the `inj₁` and `inj₂` constructors.

## Elimination

Next we describe how to consume or make use of elements of this type.

Since `Nat` is an inductive type, its eliminator is inductive as well. In fact, for a natural number, an eliminator is any proposition `P` that can use a natural number. This is proved by assuming `P zero` and some proof of inductively deducing `P (succ k)` given `P (k)` and using them to prove `P n`:

```agda
Nat-elim : (P : Nat → Set)
        → P zero
        → ((k : Nat) → P k → P (succ k))
        → (n : Nat)
        → P n
Nat-elim P p proof zero = p
Nat-elim P p proof (succ n) = proof n (Nat-elim P p proof n)
```

For function types, function application are the elimination rules. For products the elimination rules are the rules for extracting each element from a product, in other words, [fst](Types.product.html#dependent-pair-types-or-%CF%83-types) and [snd](Types.product.html#dependent-pair-types-or-%CF%83-types). For coproducts, the eliminator is also an extractor where one has to explain what to do in either case `A` or `B` pops out using [maybe](Types.product.html#eliminator).

## Computation

Computation rules describe how an eliminator acts on a constructor. For natural numbers:

```agda
Nat-comp₀ : (P : Nat → Set)
        → P zero
        → ((k : Nat) → P k → P (succ k))
        → P zero
Nat-comp₀ P p proof = Nat-elim P p proof zero

Nat-comp : (P : Nat → Set)
        → P zero
        → ((k : Nat) → P k → P (succ k))
        → (n : Nat)
        → P (succ n)
Nat-comp P p proof n = Nat-elim P p proof (succ n)
```

For function types, $ (λx.Φ)(a) ≡ substitute(a, x.Φ) $, i.e. the function is equal to substituting `a` for every occurrence of `x`. For products, the computation rule boils down to $ f : A × B → C ≡ A → B → C $, also called [currying](./Types.functions.html#currying).

## Uniqueness principle

Finally the uniqueness principle describes how functions to and from the new type are unique. For some types the uniqueness principle behaves as the dual of the computation rule by describing how constructors act on eliminators. For other types the uniqueness principle implies conditions under which functions from the new type are unique.

****
[Equational Reasoning](./Types.equational.html)

