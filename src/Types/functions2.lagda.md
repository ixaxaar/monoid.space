<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Functions, Continued](#functions-continued)
- [Classifications of functions](#classifications-of-functions)
  - [Injection](#injection)
  - [Surjection](#surjection)
  - [Bijection](#bijection)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

****
[Contents](contents.html)
[Previous](Types.functions.html)
[Next](Types.proofsAsData.html)

# Functions, Continued

```agda
module Types.functions2 where

open import Lang.dataStructures using (
  Bool; true; false;
  ℕ; List;
  one; two; three; four; five; six; seven; eight; nine; ten; zero; succ;
  _::_; [];
  ⊤; singleton; ⟂)

open import Agda.Primitive using (Level; _⊔_; lsuc)

open import Types.equality
open import Types.product using (Σ; _,_; fst; snd)
open import Types.functions
open import Types.equational
```

# Classifications of functions

Functions can be classified into:

1. Injective (one-to-one)
2. Surjective (onto)
3. Bijective (one-to-one and onto)

Note that a function, by definition, can never produce multiple outputs given the same input.

## Injection

![Figure 1: Injection](../artwork/injective.png)

A function `f : X → Y` is injective if $∀ x ∈ X, y ∈ Y, f(x) == f(y) ⟹ x == y$. Or in other words, the map is one-to-one between all objects of X and some objects of Y.

```agda
Injective : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Set (a ⊔ b)
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

record Injection {f t} (From : Set f) (To : Set t) : Set (f ⊔ t) where
  field
    to        : From → To
    injective : Injective to
```

## Surjection

![Figure 2: Surjection](../artwork/surjective.png)

A function `f : X → Y` is surjective if $∀ y ∈ Y, ∃ x ∈ X s.t. f(x) == y$. This states that for every element of Y, there should be at least one element of X such that `f(x) == y`. So Y is an complete image of X.

```agda
record Surjection {f t} (From : Set f) (To : Set t) : Set (f ⊔ t) where
  field
    to   : From → To
    from : To → From
    right-inverse-of : ∀ x → to (from x) ≡ x
```

## Bijection

![Figure 3: Bijection](../artwork/bijection.png)

Bijection is the combination of injection and surjection. A bijection implies one-to-one correspondence from the domain to the codomain − each element of one set is paired with exactly one element of the other set, and each element of the other set is paired with exactly one element of the first set. There are no unpaired elements.

```agda
record Bijection {f t} (From : Set f) (To : Set t) : Set (f ⊔ t) where
  field
    injection : Injection From To
    surjection : Surjection From To
```

****
[Proofs as Data](./Types.proofsAsData.html)
