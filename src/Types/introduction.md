****
[Contents](contents.html)
[Previous](Lang.debugging.html)
[Next](Types.universe.html)

# Introduction to Type Theory

****

- [Introduction to Type Theory](#introduction-to-type-theory)
  - [Foundations of Mathematics](#foundations-of-mathematics)
  - [Set Theory Fundamentals](#set-theory-fundamentals)
  - [Type Theory Fundamentals](#type-theory-fundamentals)
    - [Types and Terms](#types-and-terms)
    - [Judgments](#judgments)
    - [Function Types](#function-types)
    - [Dependent Types](#dependent-types)
  - [Propositions as Types (Curry-Howard Correspondence)](#propositions-as-types-curry-howard-correspondence)
  - [Inductive Types](#inductive-types)
  - [Type Classes](#type-classes)
  - [Universe Hierarchy](#universe-hierarchy)
  - [Working with Types in Practice](#working-with-types-in-practice)
    - [Pattern Matching](#pattern-matching)
    - [Recursive Functions](#recursive-functions)
    - [Dependent Pattern Matching](#dependent-pattern-matching)
  - [Applications](#applications)
  - [Comparison with Set Theory](#comparison-with-set-theory)
  - [Advanced Concepts](#advanced-concepts)


```lean
-- We'll start by importing some basic modules
import Mathlib.Data.Nat.Basic     -- For natural numbers
import Mathlib.Data.Int.Basic     -- For integers
import Mathlib.Data.List.Basic    -- For lists
import Mathlib.Data.Vector        -- For vectors
import Mathlib.Logic.Basic        -- For logical operations
```

## Foundations of Mathematics

Mathematics requires rigorous foundations (what are mathematical foundations?? like what do they even contain / mean etc??) to ensure the validity of proofs and prevent paradoxes (what?!?!?!?). Over the past century, two main foundational systems have emerged:

1. Set Theory (specifically Zermelo-Fraenkel Set Theory with Choice, ZFC)
2. Type Theory (in various forms including Martin-Löf Type Theory and Calculus of Constructions)

While both can serve as foundations, they approach mathematics in fundamentally different ways. Lean is based on type theory, specifically the Calculus of Inductive Constructions (CIC) with some extensions.

## Set Theory Fundamentals

In set theory, mathematical objects are sets, and the basic operations are set membership and set formation:

```lean
def x : Set Nat := {n | n > 0}  -- x is the set of natural numbers greater than 0
def y : Set Nat := {1, 2, 3}    -- y is the set {1, 2, 3}
```

Sets can be combined using set operations:

```lean
def z : Set Nat := x ∪ y        -- z is the union of x and y
def w : Set Nat := x ∩ y        -- w is the intersection of x and y
```

Sets also support a host of other operations, such as Cartesian products, power sets, and functions between sets. These operations can be used to define more complex mathematical structures. 19th and 20th-century mathematicians developed set theory to provide a rigorous foundation for mathematics, "foundations" in this context refers to the basic building blocks of mathematics, the axioms and rules that underpin all mathematical reasoning which are then used to prove theorems and results, whereas "paradoxes" refer to logical inconsistencies that can arise in a system of axioms and rules, such as Russell's paradox in set theory.

Set theory is the foundation of modern mathematics and provides a rich language for expressing mathematical concepts. However, it has some limitations, such as the need for a separate logic system and the potential for paradoxes (like Russell's paradox).

## Type Theory Fundamentals

### Types and Terms

The fundamental concept in type theory is that every mathematical object has a type. We write this using a colon:

```lean
def x : Nat := 5        -- x has type Nat (natural number)
def b : Bool := true    -- b has type Bool (boolean)
```

Types serve multiple roles:
- They classify mathematical objects
- They specify valid operations
- They help catch errors
- They can represent propositions (the propositions-as-types principle)

### Judgments

Type theory works with several kinds of judgments:

1. Type Formation: Defines what constitutes a valid type
```lean
#check Nat        -- Nat : Type
#check Bool       -- Bool : Type
```

2. Term Formation: Defines valid terms of a type
```lean
def valid_nat : Nat := 42
-- This would fail: def invalid_nat : Nat := true
```

3. Type Equality: When two types are considered the same
```lean
def A : Type := Nat
def B : Type := ℕ     -- ℕ is notation for Nat
-- A and B are the same type
```

4. Term Equality: When two terms are considered equal
```lean
example : 2 + 2 = 4 := rfl  -- rfl proves equality by definition
```

### Function Types

Functions are first-class citizens in type theory. A function type A → B represents functions from type A to type B:

```lean
def increment : Nat → Nat :=
  fun n => n + 1

def compose {A B C : Type} (g : B → C) (f : A → B) : A → C :=
  fun x => g (f x)
```

### Dependent Types

One of type theory's most powerful features is dependent types - types that depend on values:

```lean
def Vec (α : Type) (n : Nat) : Type :=
  {xs : List α // xs.length = n}

-- A proof that 2+2=4 has type 2+2=4
theorem two_plus_two : 2 + 2 = 4 := rfl
```

## Propositions as Types (Curry-Howard Correspondence)

In type theory, propositions are represented as types and proofs as terms of those types:

```lean
-- Logical AND corresponds to product types
example (P Q : Prop) : P ∧ Q → Q ∧ P := fun ⟨p, q⟩ => ⟨q, p⟩

-- Logical OR corresponds to sum types
example (P Q : Prop) : P ∨ Q → Q ∨ P := fun
  | Or.inl p => Or.inr p
  | Or.inr q => Or.inl q

-- Implication corresponds to function types
example (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) :=
  fun h₁ h₂ p => h₂ (h₁ p)
```

## Inductive Types

Many types in Lean are defined inductively. This means specifying:
1. Base cases (constructors with no recursive arguments)
2. Inductive cases (constructors with recursive arguments)

```lean
inductive Nat where
  | zero : Nat            -- Base case
  | succ : Nat → Nat     -- Inductive case

inductive List (α : Type) where
  | nil  : List α
  | cons : α → List α → List α
```

## Type Classes

Type classes allow ad-hoc polymorphism and overloading:

```lean
class Add (α : Type) where
  add : α → α → α

instance : Add Nat where
  add := Nat.add

#check (10 + 20)    -- Uses the Add instance for Nat
```

## Universe Hierarchy

To avoid paradoxes, Lean uses a hierarchy of universes:

```lean
#check Type        -- Type : Type 1
#check Type 1      -- Type 1 : Type 2
#check Type 2      -- Type 2 : Type 3
```

## Working with Types in Practice

### Pattern Matching

Pattern matching is a key tool for working with inductive types:

```lean
def factorial : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * factorial n
```

### Recursive Functions

Many functions are defined recursively:

```lean
def length {α : Type} : List α → Nat
  | []     => 0
  | _ :: t => 1 + length t
```

### Dependent Pattern Matching

Pattern matching becomes more powerful with dependent types:

```lean
def tail {α : Type} {n : Nat} : Vec α (n + 1) → Vec α n :=
  fun ⟨x :: xs, h⟩ => ⟨xs, sorry⟩  -- (proof omitted)
```

## Applications

Type theory and Lean have numerous applications:

1. Formal Mathematics
   - Verify complex mathematical proofs
   - Discover new mathematics through formalization

2. Program Verification
   - Prove correctness of algorithms
   - Verify safety properties of systems

3. Programming Language Theory
   - Study type systems
   - Develop new programming languages

4. Category Theory
   - Formalize categorical concepts
   - Study relationships between different structures

## Comparison with Set Theory

While set theory and type theory can both serve as foundations, they differ in important ways:

| Aspect       | Set Theory            | Type Theory            |
|--------------|-----------------------|------------------------|
| Basic notion | Membership (∈)        | Typing judgment (:)    |
| Functions    | Sets of ordered pairs | Primitive concept      |
| Logic        | Classical             | Constructive (usually) |
| Computation  | Not built-in          | Inherent               |
| Hierarchy    | Sets                  | Universe levels        |

## Advanced Concepts

Several advanced concepts build on these fundamentals:

1. Higher-Inductive Types
2. Univalence
3. Homotopy Type Theory
4. Dependent Type Theory
5. Linear Type Systems

These will be covered in later chapters.
