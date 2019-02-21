<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Decidablility](#decidablility)
  - [1. Check if a certain proposition will terminate](#1-check-if-a-certain-proposition-will-terminate)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->



# Decidablility

```agda
module Logic.decidability where

open import Lang.dataStructures using (
  Bool; true; false;
  ℕ; List;
  one; two; three; four; five; six; seven; eight; nine; ten; zero; succ;
  _::_; []
)

open import Lang.proofsAsData using (
  _<=_; ltz; lz;
  _≡_; eq₀; eq;
  _≠_; neq₀; neq₁; neq;
  _∈_; refl; succ∈
)

open import Logic.logicBasics using (
  ⟂; ⊤; ⟂-elim; ¬; contradiction; contrapos
)
```

Decidable propositions are ones whose types exist. Either we can compute `P` or `¬ P`. In the words of logic, either proposition `P` has a proof or it has been disproved:

```agda
data Dec {p} (P : Set p) : Set p where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P
```

This is also called the "law of excluded middle", which states that any proposition may either is true or its negation is true. There is no way a proposition can take on a value such as "maybe true" or "generally perceived to be false" etc.

Decidability can be pretty useful in the following ways:

## 1. Check if a certain proposition will terminate

```agda
1<2 : Dec (one <= two)
1<2 = yes (lt ltz)

1≡1 : Dec (one ≡ one)
1≡1 = yes eq₀

1≡2 : Dec (one ≡ two)
1≡2 = no ()
```

One can extract whether a given proposition is decidable as a boolean:

```agda
[_] : {P : Set} : Bool
[ yes x ] = true
[ no _ ] = false
```

Quite frequently we need to go activities in which we test if an object is of a particular type, or confirms with a given set of rules. Say, we want to test if a given number is `Even`:

```agda
data Even : ℕ → Set where
  ezero  : Even zero
  e2succ : {n : ℕ} → Even n → Even (succ (succ n))

Even? : ∀ n → Dec (Even n)
Even? zero        = yes ezero
Even? (succ zero) = no (λ ())
```


****
[Back to Contents](./contents.html)
