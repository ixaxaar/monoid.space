****
[Contents](contents.html)
[Previous](Types.universe.html)
[Next](Types.equality.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Relations](#relations)
        - [Introduction](#introduction)
        - [Types of Relations](#types-of-relations)
                - [1. Nullary Relations](#1-nullary-relations)
                - [2. Unary Relations (Predicates)](#2-unary-relations-predicates)
                - [3. Binary Relations](#3-binary-relations)
        - [Properties of Relations](#properties-of-relations)
                - [1. Reflexivity](#1-reflexivity)
                - [2. Symmetry](#2-symmetry)
                - [3. Transitivity](#3-transitivity)
        - [Relation Transformations](#relation-transformations)
                - [1. Inverse of a Relation](#1-inverse-of-a-relation)
                - [2. Composition of Relations](#2-composition-of-relations)
        - [Conclusion](#conclusion)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Relations

In mathematics and logic, relations describe how elements are connected or associated with each other. In type theory, relations are formalized as types, which allows us to reason about them using the full power of the type system.

## Types of Relations

Relations can be classified based on the number of elements they relate. They can be:
- nullary: relations that make statements about elements, also known as propositions
- unary: relations that describe properties of elements, also known as predicates
- binary: relations that describe relationships between pairs of elements

### 1. Nullary Relations (Propositions)

### 2. Unary Relations (Predicates)

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






****
[Equality](./Types.equality.html)
