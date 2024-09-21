****
[Contents](contents.html)
[Previous](Types.universe.html)
[Next](Types.equality.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Relations](#relations)
        - [Introduction](#introduction)
        - [Types of Relations](#types-of-relations)
                - [1. Nullary Relations](#1-nullary-relations)
                - [2. Unary Relations (Predicates)](#2-unary-relations-predicates)
                - [3. Binary Relations](#3-binary-relations)
        - [Properties of Relations](#properties-of-relations)
                - [1. Reflexivity](#1-reflexivity)
                - [2. Symmetry](#2-symmetry)
                - [3. Transitivity](#3-transitivity)
        - [Relation Transformations](#relation-transformations)
                - [1. Inverse of a Relation](#1-inverse-of-a-relation)
                - [2. Composition of Relations](#2-composition-of-relations)
        - [Conclusion](#conclusion)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Relations

```agda
module Types.relations where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product using (_×_; ∃; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## Introduction

In mathematics and logic, a relation is a concept that describes how elements of sets are connected or associated with each other. In type theory, relations are formalized as types, which allows us to reason about them with the full power of the type system.

## Types of Relations

Relations can be classified based on the number of elements they relate:

### 1. Nullary Relations

A nullary relation is essentially a proposition - a statement that can be true or false.

```agda
-- Representation of a nullary relation (proposition)
Prop : Set₁
Prop = Set

-- Examples of nullary relations
true-prop : Prop
true-prop = ⊤

false-prop : Prop
false-prop = ⊥
```

### 2. Unary Relations (Predicates)

A unary relation, often called a predicate, is a property that an element of a set might satisfy.

```agda
-- Definition of a predicate
Pred : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
Pred A ℓ = A → Set ℓ

-- Example: Even numbers
even : Pred ℕ lzero
even zero = ⊤
even (suc zero) = ⊥
even (suc (suc n)) = even n

-- Usage
_ : even 4 ≡ ⊤
_ = refl

_ : even 3 ≡ ⊥
_ = refl
```

### 3. Binary Relations

Binary relations describe how pairs of elements are related.

```agda
-- Definition of a binary relation
Rel : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
Rel A ℓ = A → A → Set ℓ

-- Example: Less than or equal to for natural numbers
_≤'_ : Rel ℕ lzero
zero ≤' _ = ⊤
suc m ≤' zero = ⊥
suc m ≤' suc n = m ≤' n

-- Usage
_ : 2 ≤' 4 ≡ ⊤
_ = refl

_ : 4 ≤' 2 ≡ ⊥
_ = refl
```

## Properties of Relations

Relations can have various properties that describe their behavior:

### 1. Reflexivity

A relation is reflexive if every element is related to itself.

```agda
Reflexive : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Reflexive _R_ = ∀ {x} → x R x

-- Example: ≤ is reflexive
≤-refl : Reflexive _≤_
≤-refl {zero} = z≤n
  where
    z≤n : ∀ {n : ℕ} → zero ≤ n
    z≤n {zero} = _≤_.z≤n
    z≤n {suc n} = _≤_.z≤n
≤-refl {suc n} = s≤s ≤-refl
  where
    s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n
    s≤s m≤n = _≤_.s≤s m≤n
```

### 2. Symmetry

A relation is symmetric if when x is related to y, y is also related to x.

```agda
Symmetric : {A : Set} -> Rel A -> Set
Symmetric {A} _R_  = (x y : A) -> x R y -> y R x

-- Example: Equality is symmetric
≡-sym : {A : Set}(x y : A) -> x ≡ y -> y ≡ x
≡-sym x y xy P py = xy (\z -> P z -> P x) (\px -> px) py
```

### 3. Transitivity

A relation is transitive if when x is related to y and y is related to z, then x is related to z.

```agda
Transitive : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Transitive _R_ = ∀ {x y z} → x R y → y R z → x R z

-- Example: ≤ is transitive
≤-trans : Transitive _≤_
≤-trans {zero} _ _ = Data.Nat.z≤n
≤-trans {suc x} {suc y} {suc z} (Data.Nat.s≤s x≤y) (Data.Nat.s≤s y≤z) =
  Data.Nat.s≤s (≤-trans x≤y y≤z)
≤-trans {suc x} {suc y} {zero} _ ()
≤-trans {suc x} {zero} () _
```

## Relation Transformations

We can define operations that transform relations:

### 1. Inverse of a Relation

```agda
inverse : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Rel A ℓ
inverse _R_ y x = x R y

-- Example: > is the inverse of ≤
_>_ : Rel ℕ lzero
_>_ = inverse _≤_
```

### 2. Composition of Relations

```agda
_∘R_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} → Rel A ℓ₁ → Rel A ℓ₂ → Rel A (a ⊔ ℓ₁ ⊔ ℓ₂)
(R ∘R S) x z = ∃ λ y → R x y × S y z
```

## Conclusion

Relations in type theory provide a powerful framework for expressing and reasoning about connections between elements. By formalizing relations as types, we gain access to the full expressiveness of the type system, allowing for precise and verifiable statements about the properties and behavior of relations.

This overview covers the basics of relations in type theory and Agda, including their definition, properties, and some common operations. As you delve deeper into type theory, you'll find that relations play a crucial role in many advanced concepts and proofs.

****
[Equality](./Types.equality.html)
