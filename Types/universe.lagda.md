<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Universes and families](#universes-and-families)
- [Sets](#sets)
- [Universe Polymorphism](#universe-polymorphism)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Universes and families

```agda
{-# OPTIONS --without-K #-}

module Types.universe where

open import Lang.dataStructures using (
  Bool; true; false;
  ⊥; ⊤; ℕ; List;
  _::_; [])

open import Agda.Primitive renaming (Level to AgdaLevel; lzero to alzero; lsuc to alsuc; _⊔_ to _⊔⊔_)
```

A universe is a set of types. Now, when we take our universe to be a set of types, there comes a problem of universe of all possible types, and we end up with Russel's Paradox. To avoid this, we say that our universe is constructed heirarchically, with an index `i` such that universe `Uᵢ` ∈ Uᵢ₊₁ and so on.


$$
U_{0} \in U_{1} \in U\_{2} \in ... \in U_{i} \in U_{i+1}  \in ... \in U_{\infty}
$$

Let us define the index, called `Level` in agda's standard library:

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

A "family" of types varying over a given type are called, well "families of types" :grimacing:. An example of this would be the finite set, [Fin](./dataStructures.html#finite-sequences) where every finite set has `n` elements where `n ∈ ℕ` and hence `Fin`, the creator of finite sets, is dependent on ℕ.

# Sets

Mathematical sets cannot be directly represented in Agda as they are subject to Russel's Paradox. However, sets are defined in a way similar to universes.

- Generally a set is represented by `Set₁`.
- There exist infinite other `Setᵢ` such that `Set₁ ∈ Set₂ ∈ Set₃ ∈ ...`

In fact, Ttese `Setᵢ`s serve as universes in Agda.

# Universe Polymorphism




****
[Back to Contents](./contents.html)

