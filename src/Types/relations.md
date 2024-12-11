****
[Contents](contents.html)
[Previous](Types.universe.html)
[Next](Types.equality.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Relations](#relations)
    - [Types of Relations](#types-of-relations)
    - [Nullary Relations (Propositions)](#nullary-relations-propositions)
    - [Unary Relations (Predicates)](#unary-relations-predicates)
        - [The Universal Quantifier](#the-universal-quantifier)
        - [The Existential Quantifier](#the-existential-quantifier)
    - [Binary Relations](#binary-relations)


# Relations

In mathematics and logic, relations describe how elements are connected or associated with each other. In type theory, relations are formalized as types, which allows us to reason about them using the full power of the type system.

## Types of Relations

Relations can be classified based on the number of elements they relate. They can be:
- nullary: relations that make statements about elements, also known as propositions
- unary: relations that describe properties of elements, also known as predicates
- binary: relations that describe relationships between pairs of elements

## Nullary Relations (Propositions)

## Unary Relations (Predicates)

A unary predicate is represented as a function that takes an element and returns a proposition. In simpler terms, a unary relation on type `A` is a function `A → Prop` and is a way of selecting a subset of elements from `A` based on some property. For example if `A` is `Nat` or natural numbers, a unary predicate could be `isEven` which selects all even numbers from `Nat`:

```lean
def is_even (n : Nat) : Prop := ∃ k, n = 2 * k
```

This defines a function `is_even` that takes a natural number `n` and returns a proposition stating that there exists some natural number `k` such that `n` equals `2 * k`, which is the definition of an even number.

Here is another example of a unary predicate that selects all prime numbers from `Nat`:

```
def isPrime (n : Nat) : Prop := ∀ m : Nat, m > 1 → m < n → n % m ≠ 0
```

This defines a function `isPrime` that takes a natural number `n` and returns a proposition stating that for all natural numbers `m` greater than 1 and less than `n`, `n` is not divisible by `m`.

There are a couple of things to note here:

### The Universal Quantifier

The universal quantifier `∀` can be used to define unary predicates that select all elements of a type that satisfy a given property. For example, the following unary predicate selects all natural numbers that are greater than 1:

```lean
def greaterThanOne (n : Nat) : Prop := n > 1
```
This can be expressed using the universal quantifier as follows:

```lean
def greaterThanOne (n : Nat) : Prop := ∀ m : Nat, m > 1 → m < n
```

This defines a function `greaterThanOne` that takes a natural number `n` and returns a proposition stating that:

```markdown
for all natural numbers `m` greater than 1 and less than `n`, `n` is greater than `m`.
```

The universal quantifier can be written in lean either as `∀` or `\all`. The following are a few examples of how the universal quantifier can be used:

TODO: define an algebra and explain `axiom` or import mathlib here.

```lean
#check ∀ x, (Even x ∨ Odd x) ∧ ¬ (Even x ∧ Odd x)
#check ∀ x, Even x ↔ 2 ∣ x
#check ∀ x, Even x → Even (x^2)
#check ∀ x, Even x ↔ Odd (x + 1)
```

where:
- `→` is the implication operator
- `∧` is the conjunction operator
- `∨` is the disjunction operator
- `¬` is the negation operator
- `∣` is the divisibility operator
- `^` is the exponentiation operator.

### The Existential Quantifier

The existential quantifier `∃` can be used to define unary predicates that select at least one element of a type that satisfies a given property. For example, the following unary predicate selects all natural numbers that are even:

```lean
def isEven (n : Nat) : Prop := ∃ k, n = 2 * k
```

This can be expressed using the existential quantifier as follows:

```lean
def isEven (n : Nat) : Prop := ∃ k : Nat, n = 2 * k
```

This defines a function `isEven` that takes a natural number `n` and returns a proposition stating that

```markdown
there exists some natural number `k` such that `n` equals `2 * k`,
```

i.e. an even number.

## Binary Relations

A binary relation is represented as a function that takes two elements and returns a proposition. In simpler terms, a binary relation on types `A` and `B` is a function `A → B → Prop` and is a way of describing relationships between pairs of elements. For example, a binary relation on `Nat` could be `lessThan` which selects all pairs of natural numbers `(m, n)` such that `m` is less than `n`:

```lean
def lessThan (m n : Nat) : Prop := m < n
```




****
[Equality](./Types.equality.html)
