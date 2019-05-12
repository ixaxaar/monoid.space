<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Proofs as data](#proofs-as-data)
  - [Order](#order)
  - [Odd or Even](#odd-or-even)
  - [Equality of natural numbers](#equality-of-natural-numbers)
  - [Belongs to](#belongs-to)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Proofs as data

Propositions can be defined in a recursive way such that termination of computation proves the correctness of the proof.
We use constructive proofs, as in we build the proof of a proposition (which in itself is a type) with recursion and pattern matching.

Usually, a proof consists of:
- trivial cases, serving as termination markers
- recursive pattern matchers, for constructing the proof from the trivial cases

```agda
module Lang.proofsAsData where

open import Lang.dataStructures using (
  Bool; true; false;
  ⊥; ⊤; ℕ; List;
  one; two; three; four; five; six; seven; eight; nine; ten; zero; succ;
  _::_; [])
```

## Order

For example, the `<=` operator can be defined as consisting of two constructors:

- an identity constructor `ltz` which compares any natural number with `zero`
- a successive pattern matcher `lz` which tries to reduce comparison of  `x <= y`, to `x-1 <= y-1`:

After applying `lz` sufficient number of times, if we end up at `0 <= x` where `ltz` is invoked, computation terminates and our theorem is proved.

```agda
data _<=_ : ℕ → ℕ → Set where
  ltz : {n : ℕ} → zero <= n
  lt : {m : ℕ} → {n : ℕ} → m <= n → (succ m) <= (succ n)

infix 4 _<=_
```

Some examples:

```agda
idLess₁ : one <= ten
idLess₁ = lt ltz

idLess₂ : two <= seven
idLess₂ = lt (lt ltz)

idLess₃ : three <= nine
idLess₃ = lt (lt (lt ltz))
```

If we try to compile something that is not true, the compiler will throw an error:

```haskell
idLess' : ten <= three
idLess' = lt lt lt lt lt lt lt lt lt ltz
```

```python
proofsAsData.lagda.md:68,14-16
(_m_30 <= _n_31 → succ _m_30 <= succ _n_31) !=< (nine <= two) of
type Set
```

## Odd or Even

The odd or even proofs can be defined as in the previous proof. Here we successively decrement `n` till we:

- reach `even₀` to prove `n` is even
- reach `odd₀` to prove `n` is odd

```agda
data Even : ℕ → Set
data Odd : ℕ → Set

data Even where
  zeroIsEven : Even zero
  succ : {n : ℕ} → Even n → Even (succ (succ n))

data Odd where
  oneIsOdd : Odd one
  succ : {n : ℕ} → Odd n → Odd (succ (succ n))
```

by which we could prove:

```agda
twoisEven : Even two
twoisEven = succ zeroIsEven

isFourEven : Even four
isFourEven = succ (succ zeroIsEven)

isSevenOdd : Odd seven
isSevenOdd = succ (succ (succ oneIsOdd))
```

## Equality of natural numbers

Equality of natural numbers can be proven by successively comparing decrements of them, till we reach `0 = 0`. Else the computation never terminates:

```agda
data _≡_ : ℕ → ℕ → Set where
  eq₀ : zero ≡ zero
  eq : ∀ {n m} → (succ n) ≡ (succ m)
```

Similar for not equals:

```agda
data _≠_ : ℕ → ℕ → Set where
  neq₀ : ∀ n → n ≠ zero
  neq₁ : ∀ m → zero ≠ m
  neq : ∀ { n m } → (succ n) ≠ (succ m)
```

## Belongs to

To prove that a particular element of type `A` belongs to a list `List'` of type `A`, we require:

- a reflexive constructor: `x` is always in a list containing `x` and a bunch of other elements `xs`
- a recursive pattern matcher which reduces `x ∈ list` to `x ∈ y + list₁`, which either reduces to
  - `x ∈ x + list₁` which terminates the computation or
  - `x ∈ list₁`

where `list₁` is `list` without `y`.

```agda
data _∈_ {A : Set}(x : A) : List A → Set where
  refl : ∀ {xs} → x ∈ (x :: xs)
  succ∈ : ∀ {y xs} → x ∈ xs → x ∈ (y :: xs)

infixr 4 _∈_
```

Example:

```agda
theList : List ℕ
theList = one :: two :: four :: seven :: three :: []

threeIsInList : three ∈ theList
threeIsInList = succ∈ (succ∈ (succ∈ (succ∈ refl)))
```

****
[Functions](./Lang.functions.html)

