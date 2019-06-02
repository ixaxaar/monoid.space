****
[Contents](contents.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Universes and families](#universes-and-families)
- [Sets](#sets)
- [Universe Polymorphism](#universe-polymorphism)
- [Machinery on Types](#machinery-on-types)
  - [Type of](#type-of)
  - [Equality of types](#equality-of-types)
  - [Identity type](#identity-type)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

```agda
{-# OPTIONS --without-K #-}

module Types.universe where

open import Lang.dataStructures using (
  Bool; true; false;
  ⊥; ⊤; ℕ; List;
  zero; one)

open import Agda.Primitive renaming (
  Level to AgdaLevel; 
  lzero to alzero; 
  lsuc to alsuc; 
  _⊔_ to _⊔⊔_)
```

# Universes and families

A universe can be thought of as a container for all of mathematics. There is no mathematics that is possible outside of universe. Now obviously this differs from our physical universe in a way that mathematics also describes purely conceptual stuff that need not have a physical manifestation, rather, in many ways our univrerse is a subset of the mathematical universe as it can be described by mathematical models.

For set theory, the universe can be thought as the set of all sets. For type theory, universes contain all types - hence essentially everything including objects, laws, theorems etc. The structure of the universe used in type theory are [Russel-style and Taski-style universes](http://www.cs.rhul.ac.uk/home/zhaohui/universes.pdf) though we use the former as it is easier and sufficient for our purposes. There are other kinds of universes in mathematics, for example the [Grothendieck universe](https://ncatlab.org/nlab/show/Grothendieck+universe), [Von Neumann universe](https://en.wikipedia.org/wiki/Von_Neumann_universe).

The type of all types is called `Set` in agda. Now, in constructing this type of all types naively we encounter a bunch of paradoxes, namely [Russel's Paradox](https://ncatlab.org/nlab/show/Russell%27s+paradox), [Cantor's Paradox](https://ncatlab.org/nlab/show/Cantor%27s+paradox), [Girard's Paradox](https://ncatlab.org/nlab/show/Burali-Forti%27s+paradox) etc. These can be avoided by constructing the type of all types as "universes" in a heirarchically cumulative way. When we consider our universe to be the set of all types, we say that our universe is constructed heirarchically, with an index `i` such that universe `Uᵢ` ∈ Uᵢ₊₁ and so on.

$$
U_{0} \in U_{1} \in U\_{2} \in ... \in U_{i} \in U_{i+1}  \in ... \in U_{\infty}
$$

Let us define the above index `i` of universe `Uᵢ`, called `Level` in agda's standard library:

```agda
infixl 6 _⊔_

postulate
  Level : Set
```

We define it as a postulate so we dont have to provide an implementation yet. We continue to define some operations on it, i.e.:

- `lzero`, the trivial level 0
- `lsuc` : successive iterator
- `_⊔_` : least upper bound, an operator that composes

```agda
postulate
  lzero : Level
  lsuc  : (ℓ : Level) → Level
  _⊔_   : (ℓ₁ ℓ₂ : Level) → Level
```

And finally, we define universe as:

```haskell
record Universe u e : Set (lsuc (u ⊔ e)) where
  field
    -- Codes.
    U : Set u

    -- Decoding function.
    El : U → Set e
```

![universes](universes.png)

A "family" of types varying over a given type are called, well "families of types". An example of this would be the finite set, [Fin](./dataStructures.html#finite-sequences) where every finite set has `n` elements where `n ∈ ℕ` and hence `Fin`, the creator of finite sets, is dependent on ℕ.

# Sets

Mathematical sets cannot be directly represented in Agda as they are subject to Russel's Paradox. However, sets are defined in a way similar to universes.

- Generally a set is represented by `Set₁`.
- There exist infinite other `Setᵢ` such that `Set₁ : Set₂ : Set₃ : ...`

In fact, These `Setᵢ`s are nothing but universes in Agda. Note that `Set₁` forms the large set, i.e. the set containing all sets.

In some implementations, universes are represented using a different keyword `Type` instead of `Set` in order to avoid confusing with them:

```agda
Type : (i : AgdaLevel) → Set (alsuc i)
Type i = Set i

Type₀ = Type alzero
Type0 = Type alzero

Type₁ = Type (alsuc alzero)
Type1 = Type (alsuc alzero)
```

# Universe Polymorphism

Now, given that we have infinite heirarchical universes, we would have to define the same functions, data types and machinery for each universe level, which would be pretty tedious to say the least. However, we observe how our universes are defined and note that the level-based indexing system, that connects each successive universe, provides us with the mechanics to define objects for all universe levels `ℓ`:

```agda
id : {ℓ : AgdaLevel} {A : Set ℓ} (x : A) → A
id x = x
```
Here `id` represents a family of identity functions given a type `A` and its level `ℓ`.

```agda
infixr 5 _::_
data List₁ {ℓ : AgdaLevel} (A : Set ℓ) : Set (alsuc ℓ) where
  [] : List₁ A
  _::_ : A → List₁ A → List₁ A

someList : List₁ ℕ
someList = (one :: zero :: [])

sameList : List₁ ℕ
sameList = id someList
```

# Machinery on Types

## Type of

We obviously need a means to check types:

```agda
typeof : ∀ {i} (A : Type i) (u : A) → A
typeof A u = u

infix 40 typeof
syntax typeof A u =  u :> A
```

## Equality of types

```agda
infix 30 _==_
data _==_ {i} {A : Type i} (a : A) : A → Type i where
  idp : a == a
```

## Identity type

The equality of types is itself a type - the identity type:

```agda
Path = _==_
```

****
[Relations](./Types.relations.html)

