<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Decidablility](#decidablility)
  - [Check if a certain proposition will terminate](#check-if-a-certain-proposition-will-terminate)
  - [Pattern matching](#pattern-matching)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Decidablility

```agda
module Logic.decidability where

open import Lang.dataStructures using (
  Bool; true; false;
  ℕ; List;
  one; two; three; four; five; six; seven; eight; nine; ten; zero; succ;
  _::_; [])

open import Lang.proofsAsData using (
  _≡_; eq₀; eq;
  _≠_; neq₀; neq₁; neq;
  _∈_; refl; succ∈;
  _<=_; ltz; lt)

open import Logic.logicBasics using (
  ⟂; ⊤; ⟂-elim; ¬; contradiction; contrapos)

open import Types.relations using (Rel)
```

The data types of boolean algebra that we have seen so far, come in two forms:

1. A computable form `Bool` with its objects `true` and `false`.
2. A provable form with `⊤` and `⟂` its objects.

We can always connect such forms of representation of the same underlying mathematical structures:

```agda
⤳ : Bool → Set
⤳ true = ⊤
⤳ false = ⟂
```

Decidable propositions are ones whose types exist. Either we can compute `P` or `¬ P`. In the words of logic, either proposition `P` has a proof or it has been disproved:

```agda
data Dec {p} (P : Set p) : Set p where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P
```

This is also called the "law of excluded middle", which states that any proposition may either is true or its negation is true. There is no way a proposition can take on a value such as "maybe true" or "generally perceived to be false" etc. We can write a function mapping a relation to a decidable one:

```agda
toDecidable : {A : Set} → Rel A → Set
toDecidable _∼_ = ∀ {x y} → Dec (x ∼ y)
```

Decidability can be pretty useful in the following ways:

## Check if a certain proposition will terminate

```haskell
_isLessThan_ : toDecidable _<=_
zero isLessThan _ = yes ltz
succ m isLessThan zero = no λ()
succ m isLessThan succ n with m isLessThan n
... | yes ltz = yes (lt ltz)
... | no ltz =
```

One can extract whether a given proposition is decidable as a boolean:

```agda
⌊_⌋ : {P : Set} → Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false

```

## Pattern matching

Quite frequently we need to go activities in which we test if an object is of a particular type, or confirms with a given set of rules. Say, we want to test if a given number is `Even`:

```agda
data Even : ℕ → Set where
  ezero  : Even zero
  e2succ : {n : ℕ} → Even n → Even (succ (succ n))
```


****
[Back to Contents](./contents.html)
