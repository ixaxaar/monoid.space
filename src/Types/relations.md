---

[Contents](contents.html)
[Previous](Types.universe.html)
[Next](Types.equality.html)

# Relations

---

- [Relations](#relations)
  - [Types of Relations](#types-of-relations)
  - [Nullary Relations (Propositions)](#nullary-relations-propositions)
  - [Unary Relations (Predicates)](#unary-relations-predicates)
    - [The Universal Quantifier](#the-universal-quantifier)
    - [The Existential Quantifier](#the-existential-quantifier)
  - [Binary Relations](#binary-relations)
  - [Properties of Relations](#properties-of-relations)
    - [Reflexivity](#reflexivity)
    - [Symmetry](#symmetry)
    - [Transitivity](#transitivity)
    - [Antisymmetry](#antisymmetry)

In mathematics and logic, relations describe how elements are connected or associated with each other. In type theory, relations are formalized as types, which allows us to reason about them using the full power of the type system.

## Types of Relations

Relations can be classified based on the number of elements they relate. They can be:

- nullary: relations that make statements about elements, also known as propositions
- unary: relations that describe properties of elements, also known as predicates
- binary: relations that describe relationships between pairs of elements

## Nullary Relations (Propositions)

A nullary relation is a statement that doesn't involve any variables. In type theory, these statements are represented as _propositions_.

In Lean, the type of propositions is called `Prop`. Think of a proposition as a statement that can be either true or false.

```lean
#check Prop  -- Prop : Type

-- Examples of propositions:
#check 2 + 2 = 4        -- 2 + 2 = 4 : Prop
#check 3 < 5          -- 3 < 5 : Prop
#check 1 = 0          -- 1 = 0 : Prop  (This proposition is false)

-- We can define propositions:
def is_even (n : Nat) : Prop := ∃ k, n = 2 * k

#check is_even 4  -- is_even 4 : Prop
```

In simple terms, the type Prop in Lean is used to represent statements that can be true or false (propositions).

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
def greaterThanOne (n : Nat) : Prop := ∀ k, (1 < k ∧ k < n) → False
```

This defines a function `greaterThanOne` that takes a natural number `n` and returns a proposition stating that:

```markdown
for all natural numbers `k` such that `1 < k` and `k < n`, `k` is not greater than 1, i.e. `False`.
```

The universal quantifier can be written in lean either as `∀` or `\all`. The following are a few examples of how the universal quantifier can be used:

TODO: define an algebra and explain `axiom` or import mathlib here.

```lean
import Mathlib.Data.Nat.Prime.Basic

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
def lessThanOrEqual (m n : Nat) : Prop := m ≤ n
```

Usage in raw form:

```lean
#check lessThanOrEqual 3 5
```

Infix notations can be used to make binary relations more readable. For example, the following defines a binary relation `lessThan` using the infix notation $\leqq$:

```lean
local infix:50 " ≦ " => Nat.le
```

The usage now becomes:

```
#check 3 ≦ 5
```

## Properties of Relations

Relations can have various properties such as reflexivity, symmetry, and transitivity. These properties are important for defining equivalence relations as well as mathematical structures such as groups, rings, and fields and all higher algebraic structures.

| Property     | Definition                                                                                                    | Example                                                            |
| ------------ | ------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------ |
| Reflexivity  | A relation is reflexive if every element is related to itself.                                                | `≤` is reflexive because `n ≤ n` for all natural numbers `n`.      |
| Symmetry     | A relation is symmetric if whenever `a` is related to `b`, `b` is also related to `a`.                        | `=` is symmetric because if `a = b`, then `b = a`.                 |
| Transitivity | A relation is transitive if whenever `a` is related to `b` and `b` is related to `c`, `a` is related to `c`.  | `≤` is transitive because if `a ≤ b` and `b ≤ c`, then `a ≤ c`.    |
| Antisymmetry | A relation is antisymmetric if whenever `a` is related to `b` and `b` is related to `a`, `a` is equal to `b`. | `≤` is antisymmetric because if `a ≤ b` and `b ≤ a`, then `a = b`. |

Spefial combinations of these properties give rise to other important properties such as equivalence relations, partial orders, and total orders that we will look at later.

### Reflexivity

A relation is reflexive if every element is related to itself. For example, the relation `≤` is reflexive because `n ≤ n` for all natural numbers `n`. The property of reflexivity can be expressed as follows:

```lean
def reflexive {A : Type} (R : A → A → Prop) : Prop := ∀ a : A, R a a
```

This defines a function `reflexive` that takes a relation `R` on type `A` and returns a proposition stating that for all elements `a` of type `A`, `a` is related to itself.

### Symmetry

A relation is symmetric if whenever `a` is related to `b`, `b` is also related to `a`. For example, the relation `=` is symmetric because if `a = b`, then `b = a`. The property of symmetry can be expressed as follows:

```lean
def symmetric {A : Type} (R : A → A → Prop) : Prop := ∀ a b : A, R a b → R b a
```

This defines a function `symmetric` that takes a relation `R` on type `A` and returns a proposition stating that for all elements `a` and `b` of type `A`, if `a` is related to `b`, then `b` is related to `a`.

### Transitivity

A relation is transitive if whenever `a` is related to `b` and `b` is related to `c`, `a` is related to `c`. For example, the relation `≤` is transitive because if `a ≤ b` and `b ≤ c`, then `a ≤ c`. The property of transitivity can be expressed as follows:

```lean
def transitive {A : Type} (R : A → A → Prop) : Prop := ∀ a b c : A, R a b → R b c → R a c
```

This defines a function `transitive` that takes a relation `R` on type `A` and returns a proposition stating that for all elements `a`, `b`, and `c` of type `A`, if `a` is related to `b` and `b` is related to `c`, then `a` is related to `c`.

### Antisymmetry

A relation is antisymmetric if whenever `a` is related to `b` and `b` is related to `a`, `a` is equal to `b`. For example, the relation `≤` is antisymmetric because if `a ≤ b` and `b ≤ a`, then `a = b`. The property of antisymmetry can be expressed as follows:

```lean
def antisymmetric {A : Type} (R : A → A → Prop) : Prop := ∀ a b : A, R a b → R b a → a = b
```

This defines a function `antisymmetric` that takes a relation `R` on type `A` and returns a proposition stating that for all elements `a` and `b` of type `A`, if `a` is related to `b` and `b` is related to `a`, then `a` is equal to `b`.

---

[Equality](./Types.equality.html)
