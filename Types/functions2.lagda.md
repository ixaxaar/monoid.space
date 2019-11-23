<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Functions, Continued...](#functions-continued)
- [Classifications of functions](#classifications-of-functions)
  - [Injection](#injection)
  - [Surjection](#surjection)
  - [Bijection](#bijection)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

****
[Contents](contents.html)
[Previous](Types.functions.html)
[Next](Types.proofsAsData.html)

# Functions, Continued...

```agda
module Types.functions2 where

open import Lang.dataStructures using (
  Bool; true; false;
  ℕ; List;
  one; two; three; four; five; six; seven; eight; nine; ten; zero; succ;
  _::_; [];
  ⊤; singleton; ⟂)

open import Agda.Primitive using (Level; _⊔_; lsuc)

open import Types.equality using (IsEquivalence; Setoid; Rel)
open import Types.product using (Σ; _,_; fst; snd)
open import Types.functions
```

# Classifications of functions

Functions can be broadly classified as:

1. Injective (one-to-one)
2. Surjective (onto)
3. Bijective (one-to-one and onto)

![Injection vs Surjection vs Bijection](functions.png)

Note that a function, by definition, can never produce multiple outputs given the same input.

## Injection

A function `f : X → Y` is injective if $∀ x ∈ X, y ∈ Y, f(x) == f(y) ⟹ x == y$. Or in other words, the map is one-to-one between all objects of X and some objects of Y.

```agda
module _ {a b ℓ}
        {A : Set a}
        {B : A → Set b}
        {_=₁_ : Rel A ℓ}
        {_=₂_ : (x : A) → Rel (B x) ℓ}
        (eq1 : IsEquivalence _=₁_)
        (eq2 : (x : A) → IsEquivalence (_=₂_ x))
        where
```

  Injective : A → B → Set _
  Injective f = ∀ {x y : A} → (f x) _=₁_ (f y) → x (_=₂_ x) y

## Surjection

A function `f : X → Y` is surjective if $∀ y ∈ Y, ∃ x ∈ X s.t. f(x) == y$. This states that for every element of Y, there should be at least one element of X such that `f(x) == y`. So Y is an complete image of X.

## Bijection

Bijection is the combination of injection and surjection.


****
[Proofs as Data](./Types.proofsAsData.html)
