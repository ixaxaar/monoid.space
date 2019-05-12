<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Syntactic quirks](#syntactic-quirks)
- [Syntactic sugars](#syntactic-sugars)
  - [Abstracting common parameters](#abstracting-common-parameters)
  - [Abstracting parameters from constructors to types](#abstracting-parameters-from-constructors-to-types)
  - [Implicit arguments](#implicit-arguments)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Syntactic quirks

Agda, being a pretty obscure language, inspite of having no dearth of documentation, still tends to lack some where it gets most confusing. We capture some of them here.

```agda
module Lang.syntaxQuirks where

open import Lang.dataStructures using (
  Bool; true; false;
  ⊥; ⊤; ℕ; List;
  one; two; three; four; five; six; seven; eight; nine; ten; zero; succ;
  _::_; [];
  Vec; cons; vec3)
```

# Syntactic sugars

Mostly short-forms of various stuff used more often.

## Abstracting common parameters

```haskell
data _≤′_ : ℕ → ℕ → Set where
  ≤′-refl : {m : ℕ} →                       m ≤′ m
  ≤′-step : {m : ℕ} → {n : ℕ} →  m ≤′ n  →  m ≤′ succ n
```

is similar to

```haskell
data _≤′₁_ (m : ℕ) : ℕ → Set where
  ≤′₁-refl :                       m ≤′₁ m
  ≤′₁-step : {n : ℕ} →  m ≤′₁ n  →  m ≤′₁ succ n
```

## Abstracting parameters from constructors to types

```haskell
data _≤″_ : ℕ → ℕ → Set where
  ≤+ : ∀ {m n k} → m + n ≡ k → m ≤″ k
```

is similar to

```haskell
data _≤″₁_ (m : ℕ) : ℕ → Set where
  ≤+ : ∀ {n k} → m + n ≡ k → m ≤″₁ k
```

which is similar to

```haskell
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

Though these are generally ill-advised as they may cause significant confusion when used unwisely.

****
[Modules, Records and Postulates](./Lang.other.html)
