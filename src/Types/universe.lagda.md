****
[Contents](contents.html)
[Previous](Types.introduction.html)
[Next](Types.relations.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Universes and Families](#universes-and-families)
  - [Introduction to Universes](#introduction-to-universes)
  - [Universes in Agda](#universes-in-agda)
  - [Universe Levels](#universe-levels)
  - [Universe Polymorphism](#universe-polymorphism)
  - [Cumulativity](#cumulativity)
  - [The Prop Universe](#the-prop-universe)
  - [Families of Types](#families-of-types)
  - [Machinery on Types](#machinery-on-types)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Universes and Families

```agda
module Types.universe where

open import Agda.Primitive renaming (Prop to UProp)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_)
```

## Introduction to Universes

A `universe` can be thought of as a container for all of mathematics within a certain scope. There is no mathematics that is possible outside of its universe. In type theory, we often work with universes of types, which contain all types we can work with at a certain level.

Formally, the structure of the universe used in type theory are Russell-style and Tarski-style universes, though we use the former as it is easier and sufficient for our purposes. There are other kinds of universes in mathematics, for example the Grothendieck universe and Von Neumann universe.

## Universes in Agda

In Agda, the type of all types is called `Set`. However, to avoid paradoxes like Russell's Paradox, Cantor's Paradox, and Girard's Paradox, Agda uses a hierarchy of universes:

- Every Agda type is of type `Set`, i.e., `Set : Set₁`.
- Each universe level is an element of the next universe level: `Setᵢ : Setᵢ₊₁`.
- There exist infinite universe levels in Agda: `Set : Set₁ : Set₂ : Set₃ : ...`.

Here's a simple demonstration:

```agda
_ : Set
_ = ℕ

_ : Set₁
_ = Set

_ : Set₂
_ = Set₁
```

## Universe Levels

Agda provides a special type `Level` to represent universe levels:

```agda
-- Already imported from Agda.Primitive:
-- Level : Set
-- lzero : Level
-- lsuc  : Level → Level
-- _⊔_   : Level → Level → Level

-- Examples:
level-example : Level
level-example = lsuc (lsuc lzero)  -- represents Set₂

max-level : Level → Level → Level
max-level = _⊔_
```

## Universe Polymorphism

Universe polymorphism allows us to define functions and types that work across all universe levels:

```agda
id : ∀ {ℓ} {A : Set ℓ} → A → A
id x = x

data Maybe {ℓ} (A : Set ℓ) : Set ℓ where
  Just    : A → Maybe A
  Nothing : Maybe A

map-maybe : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → Maybe A → Maybe B
map-maybe f (Just x)  = Just (f x)
map-maybe f Nothing   = Nothing
```

## Cumulativity

Agda's universe hierarchy is cumulative, meaning that types from lower universes can be used in higher universes:

```agda
record Lift {a ℓ} (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field
    lower : A

lift-type : ∀ {ℓ} → Set ℓ → Set (lsuc ℓ)
lift-type {ℓ} A = Lift {ℓ} {lsuc ℓ} A

nat-in-higher-universe : Set₁
nat-in-higher-universe = lift-type ℕ
```

```agda
-- Creating a lifted value
lifted-five : nat-in-higher-universe
lifted-five = lift 5

-- Extracting the original value
original-five : ℕ
original-five = Lift.lower lifted-five
```

## The Prop Universe

Some type theories include a separate universe `Prop` for propositions. While standard Agda doesn't have this, we can simulate it:

```agda
data Prop : Set₁ where
  True  : Prop
  False : Prop
  And   : Prop → Prop → Prop
  Or    : Prop → Prop → Prop

⟦_⟧ : Prop → Set
⟦ True ⟧      = ⊤
⟦ False ⟧     = ⊥
⟦ And p q ⟧   = ⟦ p ⟧ × ⟦ q ⟧
⟦ Or p q ⟧    = ⟦ p ⟧ ⊎ ⟦ q ⟧
```

## Families of Types

A "family" of types varying over a given type are called "families of types". An example is the finite set type `Fin n`, where `n : ℕ`:

```agda
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)
```

## Machinery on Types

Here are some utility functions for working with types:

```agda
-- Type of
typeof : ∀ {ℓ} (A : Set ℓ) (x : A) → A
typeof A x = x

syntax typeof A x = x :> A

-- Equality of types
data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

infix 4 _≡_

-- The identity type, also known as the Path type in Homotopy Type Theory
Path : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
Path = _≡_
```

The `Path` type is fundamental in Homotopy Type Theory, where it represents paths or equivalences between two points in a space. This connection between type theory and homotopy theory leads to powerful new ways of thinking about equality and structure in mathematics.

****
[Relations](./Types.relations.html)
