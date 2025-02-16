****
[Contents](contents.html)
[Previous](Lang.debugging.html)
[Next](Types.universe.html)

# Introduction to Type Theory

****

- [Introduction to Type Theory](#introduction-to-type-theory)
  - [Foundations of Mathematics](#foundations-of-mathematics)
  - [Set Theory Fundamentals](#set-theory-fundamentals)
    - [Construction](#construction)
    - [Membership and Subsets](#membership-and-subsets)
    - [Set Operations](#set-operations)
    - [Properties of Set Operations](#properties-of-set-operations)
  - [Type Theory Fundamentals](#type-theory-fundamentals)
    - [Types and Terms](#types-and-terms)
    - [Judgments](#judgments)
      - [1. Type Formation: Defines what constitutes a valid type](#1-type-formation-defines-what-constitutes-a-valid-type)
      - [2. Term Formation: Defines valid terms of a type](#2-term-formation-defines-valid-terms-of-a-type)
      - [3. Type Equality: When two types are considered the same](#3-type-equality-when-two-types-are-considered-the-same)
      - [4. Term Equality: When two terms are considered equal](#4-term-equality-when-two-terms-are-considered-equal)
  - [Applications](#applications)
    - [Computer Science](#computer-science)
    - [Mathematics](#mathematics)
  - [Advanced Concepts and Implications](#advanced-concepts-and-implications)
    - [Categorical Interpretations](#categorical-interpretations)
    - [Homotopy Type Theory](#homotopy-type-theory)
    - [Proof Assistants and Formal Verification](#proof-assistants-and-formal-verification)


```lean
import Mathlib.Data.Nat.Basic     -- For natural numbers
import Mathlib.Data.Int.Basic     -- For integers
import Mathlib.Data.List.Basic    -- For lists
import Mathlib.Data.Vector        -- For vectors
import Mathlib.Logic.Basic        -- For logical operations
import Mathlib.Data.Set.Basic     -- For set operations
```

## Foundations of Mathematics

At the very base of mathematics, we have the concept of sets, which are collections of objects. Set theory provides a formal language for defining and manipulating these collections. Set theory forms the programming language of mathematics, allowing us to express mathematical concepts and operations in a precise and unambiguous way. All mathematical structures can be built from sets, and all machinery operating on these structures can be expressed in terms of set operations. Mathematics is built on a foundation of axioms and rules that define the basic concepts and operations used in mathematical reasoning. These foundations provide a framework for proving theorems and establishing the validity of mathematical results.

Set theory, however, is not the only foundational system for mathematics. Over the past century, another foundational system has emerged: type theory. Type theory is a formal system that classifies mathematical objects by their types and specifies valid operations on these objects. In type theory, every mathematical object has a type, and types serve multiple roles, such as classifying objects, specifying operations, catching errors, and representing propositions. Type theory provides a different perspective on mathematics, emphasizing the structure of mathematical objects and the relationships between them.

While both set theory and type theory can serve as foundations for mathematics, they approach mathematical reasoning in fundamentally different ways. Lean, like several other modern proof assistants, is based on type theory. This choice enables Lean to provide powerful tools for both mathematical reasoning and computation. Practically, using Lean, and hence type theory, instead of set theory implies we can automatically check proofs, instead of the ultra-tedious manual checking that would be required in set theory. This is because Lean's type theory is designed to be computable, which means that we can write programs that manipulate proofs and terms. This is a significant advantage over set theory, where proofs are typically written in natural language and must be checked manually by humans, who tend to make their own mistakes.

## Set Theory Fundamentals

In set theory, mathematical objects are sets. Here we cover the very basics of sets and their operations.

### Construction

Sets can be constructed by enumerating their elements. For example, `x` is a set containing the natural numbers 1, 2, and 3:

```lean
def y : Set Nat := {1, 2, 3}    -- y is the set {1, 2, 3}
```

Sets can also be constructed by the builder notation {x | P x}, where P x is a predicate that specifies the objects that belong to the set. For example, `x` is a set of natural numbers greater than 0:

```lean
def x : Set Nat := {n | n > 0}  -- x is the set of natural numbers greater than 0
```

### Membership and Subsets

Set membership is denoted by the symbol ∈. It implies that an object, `x`, belongs to a set, for example here `x` belongs to the set of natural numbers `Nat`:

```lean
def x : Set Nat := {n | n > 0}  -- x is the set of natural numbers greater than 0
```

Subsets are denoted by the symbol ⊆. It implies that a set, `y`, is a subset of another set, `x`:

```lean
def y : Set Nat := {n | n > 1}  -- y is the set of natural numbers greater than 1
def z : Bool := y ⊆ x           -- z is true because y is a subset of x
```

### Set Operations

Sets can be combined using set operations. For example, the union of two sets `x` and `y` is a set containing all elements that belong to either `x` or `y`:

```lean
def x : Set Nat := {1, 2, 3}    -- x is the set {1, 2, 3}
def y : Set Nat := {3, 4, 5}    -- y is the set {3, 4, 5}

def z : Set Nat := x ∪ y        -- z is the union of x and y
```

Similarly, the intersection of two sets `x` and `y` is a set containing all elements that belong to both `x` and `y`:

```lean
def z : Set Nat := x ∩ y        -- z is the intersection of x and y
```

Sets can have complements, which are the elements that do not belong to the set:

```lean
def z : Set Nat := xᶜ          -- z is the complement of x
```

There is a special set, the empty set, denoted by ∅, which contains no elements:

```lean
def z : Set Nat := ∅            -- z is the empty set
```

and power sets, which are sets of all subsets of a given set:

```lean
def z : Set (Set Nat) := 𝒫 x    -- z is the power set of x
```

### Properties of Set Operations

The operations on sets have several properties. For example, the following properties hold for union and intersection:

1. Commutativity: The order of sets does not matter for union and intersection:

```lean
def x : Set Nat := {1, 2, 3}
def y : Set Nat := {3, 4, 5}

#check x ∪ y -- Set Nat
#check y ∪ x -- Set Nat
```

Here, $z_{1}$, $z_{2}$, and $z_{3}$ are equivalent.

2. Associativity: The grouping of sets does not matter for union and intersection:

```lean
def z : Set Nat := {5, 6, 7}

#check x ∪ (y ∪ z) -- Set Nat
#check (x ∪ y) ∪ z -- Set Nat
```

Here, $z_{1}$ and $z_{2}$ are equivalent.

3. Distributivity: Union and intersection distribute over each other:

```lean
#check x ∪ (y ∩ z)
#check (x ∪ y) ∩ (x ∪ z)
```

Here, $z_{1}$ and $z_{2}$ are equivalent.

4. Idempotence: Repeated union or intersection with the same set does not change the set:

```lean
#check x ∪ x
#check x ∩ x
```

Here, $z_{1}$ and $z_{2}$ are equivalent to $x$.

5. Identity: The empty set is the identity for union and the universal set is the identity for intersection:

```lean
def z₁ : Set Nat := x ∪ ∅
def z₂ : Set Nat := x ∩ {n | n > 0}
```

Here, $z_{1}$ is equivalent to $x$ and $z_{2}$ is equivalent to $x$.

6. Distributivity of union over intersection: Union operation distributes over intersection:

```lean
def z₁ : Set Nat := x ∪ (y ∩ z)
def z₂ : Set Nat := (x ∪ y) ∩ (x ∪ z)
```

Here, $z_{1}$ and $z_{2}$ are equivalent.

There are several other properties of set operations, which are used in mathematical reasoning and proofs, and we are going to skip those as styduing them is not the goal of this book.

## Type Theory Fundamentals

### Types and Terms

The fundamental concept in type theory is that every mathematical object has a type. We write this using a colon:

```lean
def x : Nat := 5        -- x has type Nat (natural number)
def b : Bool := true    -- b has type Bool (boolean)
```

A `Type` in mathematics and computer science is a collection of objects that share common properties. In type theory, types classify mathematical objects and specify valid operations on them. For example, the type `Nat` represents the set of natural numbers, and the type `Bool` represents the set of boolean values. Types can also represent propositions, as we will see later.

Types serve multiple roles:

- They classify mathematical objects, as in all objects of a type share common properties.
- They specify valid operations on objects of a type.
- They can represent propositions (the propositions-as-types principle).

Generally, a "theory" in mathematics can be constructed using type theory by defining the types of objects in the theory and the operations that can be performed on them. This is similar to how a "theory" in set theory can be constructed by defining the sets of objects in the theory and the operations that can be performed on them.

A term is an object of a type. For example, `5` is a term of type `Nat`, and `true` is a term of type `Bool`. Terms can be combined using operations defined on their types. For example, we can add two natural numbers:

```lean
def x : Nat := 5
def y : Nat := 10
def z : Nat := x + y
```

Here, `z` is a term of type `Nat` obtained by adding `x` and `y`.

### Judgments

Judgements are statements about types and terms in type theory. They are used to define what constitutes a valid type, a valid term of a type, and when two types or terms are considered equal. Type theory works with several kinds of judgments:

#### 1. Type Formation: Defines what constitutes a valid type

```lean
#check Nat        -- Nat : Type
#check Bool       -- Bool : Type
```

Formally, a type is a valid type if it is a member of the universe of types.

#### 2. Term Formation: Defines valid terms of a type

```lean
def valid_nat : Nat := 42
-- This would fail: def invalid_nat : Nat := true
```

Formally, a term is a valid term of a type if it is a member of the set of terms of that type. Consider the type `Nat` as the set of natural numbers. Then, `42` is a valid term of type `Nat`, while `true` is not.

#### 3. Type Equality: When two types are considered the same

Lean provides a way to state basic equalities using `=`. We have the principle that every value is equal to itself: which is the principle of reflexivity.

For example:

```lean
#check 2 + 2 = 4
```
The `rfl` tactic stands for "reflexivity." It allows Lean to acknowledge this simple kind of equality, where something is clearly equal to itself *by definition*:
```lean
example : 2 + 2 = 4 := rfl  -- 2 + 2 reduces to 4 definitionally.
```
`rfl` proofs that the two sides of the equality (`=`) are definitionally equal.

There are three kinds of equality in type theory:

- **Definitional Equality**: Equality by definition (what Lean's #reduce shows).
- **Propositional Equality**: Equality expressed as a proposition (the = we've been using). This kind of equality is non-trivial and needs to be proved.
- **Judgmental Equality**: A lower-level notion of equality that is built into Lean's type checker.

#### 4. Term Equality: When two terms are considered equal

```lean
example : 2 + 2 = 4 := rfl  -- rfl proves equality by definition
```

Here, `rfl` is a proof that `2 + 2` is equal to `4`, where `rfl` denotes reflexivity property of equality which states that every term is equal to itself, or if `x` is equal to `y`, then `y` is equal to `x`.

We will further explore type theory in the following sections.

## Applications

### Computer Science

Type Theory has found extensive applications in computer science:

1. **Programming Language Design**: Many modern programming languages incorporate ideas from Type Theory in their type systems.

2. **Formal Verification**: Type Theory provides a basis for proving properties of programs and verifying their correctness.

3. **Proof Assistants**: Software like Coq, Agda, and Lean, based on Type Theory, allow for computer-assisted theorem proving.

4. **Foundations of Computer Science**: Type Theory provides a theoretical foundation for understanding computation and programming languages.

### Mathematics

While Set Theory remains the most common foundation for mathematics, Type Theory offers some advantages:

1. **Constructive Mathematics**: Type Theory naturally supports constructive approaches to mathematics.

2. **Computational Content**: Proofs in Type Theory often have direct computational interpretations.

3. **Higher-Order Logic**: Type Theory easily accommodates higher-order logic, which can be more expressive than first-order logic used in Set Theory.

4. **Homotopy Type Theory**: Recent developments have connected Type Theory with modern areas of mathematics like homotopy theory.

## Advanced Concepts and Implications

### Categorical Interpretations

Both Set Theory and Type Theory have important connections to Category Theory, a branch of mathematics that deals with abstract structures and relationships between them.

1. **Set Theory and Categories**:
   - The category Set, whose objects are sets and morphisms are functions, is a fundamental example in category theory.
   - Many set-theoretic constructions have categorical generalizations (e.g., products, coproducts, exponentials).

2. **Type Theory and Categories**:
   - There's a deep connection between Type Theory and Cartesian closed categories.
   - Each type theory gives rise to a category, where types are objects and terms are morphisms.

### Homotopy Type Theory

Homotopy Type Theory (HoTT) is a recent development that connects Type Theory with abstract homotopy theory.

1. **Univalence Axiom**: This axiom in HoTT states that isomorphic types are equal, providing a powerful principle for reasoning about equivalence.

2. **Inductive Types with Recursion**: HoTT extends Type Theory with inductive types and recursion principles, allowing for the construction of complex structures like higher inductive types.

### Proof Assistants and Formal Verification

The development of proof assistants based on Type Theory has significant implications for mathematics and computer science.

1. **Formalized Mathematics**: Large parts of mathematics have been formalized in systems like Coq, Lean, and Agda, and is the basic reason why we are here!

2. **Software Verification**: Type Theory-based systems are used to verify the correctness of critical software systems.

Example (CompCert, a verified C compiler).

****

[Universes and families](./Types.universe.html)
