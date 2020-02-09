****
[Contents](contents.html)
[Previous](Lang.other.html)
[Next](Lang.debugging.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Syntactic quirks](#syntactic-quirks)
- [Syntactic sugars](#syntactic-sugars)
  - [Common parameters](#common-parameters)
  - [Different ways of defining `data`](#different-ways-of-defining-data)
  - [Implicit arguments](#implicit-arguments)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Syntactic quirks

We capture here some of the caveats and syntactic sugars here.

```agda
module Lang.syntaxQuirks where

open import Lang.dataStructures
open import Agda.Builtin.Equality
```

# Syntactic sugars

Mostly short-forms of various stuff used more often.

## Common parameters

The implicit parameter `{m : ℕ}` common to all constructors can be abstracted out into the data definition:

```agda
data _≤′_ : ℕ → ℕ → Set where
  ≤′-refl : {m : ℕ} →                       m ≤′ m
  ≤′-step : {m : ℕ} → {n : ℕ} →  m ≤′ n  →  m ≤′ succ n
```

is same as

```agda
data _≤′₁_ (m : ℕ) : ℕ → Set where
  ≤′₁-refl :                       m ≤′₁ m
  ≤′₁-step : {n : ℕ} →  m ≤′₁ n  →  m ≤′₁ succ n
```

## Different ways of defining `data`

The previous technique also works for concrete parameters:

```agda
data _≤″_ : ℕ → ℕ → Set where
  ≤″ : ∀ {m n k} → m + n ≡ k → m ≤″ k
```

is same as

```agda
data _≤″₁_ (m : ℕ) : ℕ → Set where
  ≤+ : ∀ {n k} → m + n ≡ k → m ≤″₁ k
```

which is same as

```agda
data _≤″₂_ (m : ℕ) (k : ℕ) : Set where
  ≤+ : ∀ {n} → m + n ≡ k → m ≤″₂ k
```

## Implicit arguments

Arguments that can be inferred by the compiler can be left out with an `_`:

```agda
length : (A : Set) (len : ℕ) → Vec A len → ℕ
length A zero [] = zero
length A len somevec = len
```

```agda
length' : (A : Set) (len : ℕ) → Vec A len → ℕ
length' A zero [] = zero
length' A len _   = len
```

```agda
length'' : (A : Set) (len : ℕ) → Vec A len → ℕ
length'' A zero [] = zero
length'' _ len _   = len
```

Though these are generally ill-advised as they may cause confusion when used unwisely.

****
[Modules, Records and Postulates](./Lang.other.html)
