<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Equalities](#equalities)
  - [Propositional Equality](#propositional-equality)
      - [Symmetry](#symmetry)
      - [Transitivity](#transitivity)
    - [Functions that preserve equality or Congruence](#functions-that-preserve-equality-or-congruence)
    - [Substitution](#substitution)
    - [](#)
- [Definitonal Equality](#definitonal-equality)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Equalities

```agda
module Types.equality where

open import Lang.dataStructures using (
  Bool; true; false;
  ⊥; ⊤; ℕ; List;
  one; two; three; four; five; six; seven; eight; nine; ten; zero; succ;
  _::_; [])
```

There are different kinds equivalence relations and hence, equalities in type theory.

## Propositional Equality

In type theory, all proofs can be represented as a type. Propositional equality is a kind of equality which requires a proof, and hence the equality itself is also a type `≡`:

```agda
infix 4 _≡_

data _≡_ {A : Set}(a : A) : {B : Set} → B → Set where
  refl : a ≡ a
```

Reflexivity is defined with the definition of `≡` by the special keyword in Agda, called `refl`, the others being:

#### Symmetry

```agda
symmetry : ∀ {A B}{a : A}{b : B}
  → a ≡ b
  → b ≡ a
symmetry refl = refl
```

#### Transitivity

```agda
transitivity : ∀ {A B C}{a : A}{b : B}{c : C}
  → a ≡ b
  → b ≡ c
  → a ≡ c
transitivity refl p = p
```

### Functions that preserve equality or Congruence

Functions that when applied to objects of a type, do not alter the operation of equality can be defined as:

```agda
congruence : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
  → f x ≡ f y
congruence f refl = refl
```

### Substitution

If `a = b` and if `predicate a = true` ⟹ `predicate b = true`

```agda
substitution : ∀ {A : Set} {x y : A} (Predicate : A → Set)
  → x ≡ y
  → Predicate x
  → Predicate y
substitution Predicate refl p = p
```

###

Finally, our table example:

```agda
data Table : Set where
  generic : Table
  specific : ℕ → Table

tableEqZero : generic ≡ generic
tableEqZero = refl

tableEqThree : (specific three) ≡ (specific three)
tableEqThree = refl
```

This, of course does not compile:

```haskell
tableEqNot : generic ≡ (specific three)
tableEqNot = refl
```

# Definitonal Equality

Definitonal equality relates to the Agda compiler's own integrity check through which a statement is deemed true or correctly compiled. Hence every statemtent has its own notion of equality.

```agda
defEqual₁ : ℕ
defEqual₁ = seven

defEqual₂ : ℕ
defEqual₂ = seven
```

Here, `defEqual₁` and `defEqual₂` both are of type `ℕ` and hence definitionally equal is known to the compiler.

****
[Back to Contents](./contents.html)
