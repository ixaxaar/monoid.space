---

[Contents](contents.html)
[Previous](Lang.debugging.html)
[Next](Types.universe.html)

# Introduction to Type Theory

---

- [Introduction to Type Theory](#introduction-to-type-theory)
  - [Foundations of Mathematics](#foundations-of-mathematics)
  - [Set Theory](#set-theory)
    - [Construction](#construction)
    - [Membership and Subsets](#membership-and-subsets)
    - [Set Operations](#set-operations)
    - [Properties of Set Operations](#properties-of-set-operations)
  - [Type Theory](#type-theory)
    - [Types, Terms, and Judgments](#types-terms-and-judgments)
    - [Type Formation](#type-formation)
    - [Term Formation](#term-formation)
    - [Type Equality](#type-equality)
    - [Term Equality](#term-equality)
    - [Advantages of Type Theory](#advantages-of-type-theory)
    - [Applications](#applications)
      - [Computer Science](#computer-science)
      - [Mathematics](#mathematics)

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

## Set Theory

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

## Type Theory

Type theory is a formal system that serves as an alternative foundation for mathematics and computer science, distinct from set theory. Instead of building everything from sets, type theory centers around the concept of types. Crucially, every object in type theory has a type. This is a fundamental and pervasive principle. Type theory provides an emphasis on computation and is well-suited for formal verification and automated proof checking, as implemented in proof assistants like Lean.

### Types, Terms, and Judgments

The core building blocks of type theory are:

- **Types:** These represent collections of objects with shared properties. Think of familiar examples like `Nat` (natural numbers) or `Bool` (booleans). But types can be much more sophisticated, representing functions, propositions, and complex data structures.
- **Terms:** These are the individual objects that inhabit types. For example, `5` is a term of type `Nat`, and `true` is a term of type `Bool`. We use the notation `a : A` to say that term `a` has type `A`.
- **Judgments:** These are the fundamental assertions we make within type theory. They are _not_ propositions that can be true or false within the system; instead, they are declarations about the validity of types and terms. There are four main kinds of judgments:

### Type Formation

This judgment asserts that something is a well-formed type. In Lean:

```lean
#check Nat        -- Nat : Type
#check Bool       -- Bool : Type
#check Nat → Bool  -- Nat → Bool : Type (Functions from Nat to Bool)
```

Formally, the judgment `A : Type` (or sometimes `A type`, depending on the specific type theory) means that `A` is a valid type. This is not something you prove within the system; it's a foundational assertion established by rules. The notation `#check` will only succeed for well formed types.

### Term Formation

This judgment asserts that a term belongs to a specific type:

```lean
#check (5 : Nat)      -- 5 : Nat
#check (true : Bool)   -- true : Bool

def myNumber : Nat := 5
#check myNumber       -- myNumber : Nat

-- Example of an ill-typed term (this would cause an error):
-- def badNumber : Nat := true  -- Error: type mismatch
```

Formally, `a : A` means "term `a` has type `A`". Again, this is not a proposition to be proven, but a declaration based on the rules of type theory. Lean's type checker enforces these rules. If you try to construct a term that violates the typing rules, Lean will report an error.

### Type Equality

This judgment asserts that two types are definitionally equal. This is a very strong form of equality. It means they are the same type, not just equivalent in some way. This is often written as `A ≡ B` or (in some contexts) just `A = B` (but be careful – in a type theory, equality can mean different things). Lean handles definitional equality internally.

```lean
-- Example (though Lean infers this automatically)
def MyType : Type := Nat
#check MyType -- MyType : Type, which is definitionally equal to Nat.
```

In this simple case, the type `MyType` on the right hand side is defined as equal to the `Nat`. With a simple equality, this is a _definitional equality_. Other examples are provided below.

### Term Equality

This judgment has two main forms, with critical distinctions:

- **Definitional Equality (≡):** Two terms are definitionally equal if they reduce to the same normal form. This is like saying `2 + 2` and `4` are definitionally equal. Lean checks this automatically.

```lean
example : 2 + 2 = 4 := rfl  -- Success!  2 + 2 and 4 are definitionally equal.
```

`rfl` (reflexivity) works precisely because `2 + 2` and `4` are _definitionally_ equal. Lean can see this directly, without further proof steps.

- **Propositional Equality (=):** This is the more familiar notion of equality, expressed as a _proposition_ that can be proven. `a = b` (where `a` and `b` are terms of the same type) is itself a _type_! This is where the _propositions-as-types_ principle comes in (which we'll cover later, but it's good to be aware of it early). Proving `a = b` involves constructing a _term_ of that type.

```lean
-- An easy example, still provable by rfl because of definitional equality
example : (2 + 2 : Nat) = (4 : Nat) := rfl

-- A slightly more interesting example, requiring a proof (using theorems)
example (n : Nat) : n + 0 = n := Nat.add_zero n
```

Crucially, definitional equality implies propositional equality, but _not_ the other way around. If `a ≡ b`, then `a = b` is trivially provable (with `rfl`).

### Advantages of Type Theory

- **Computability:** Type theory is inherently computational. Terms can be evaluated, and type checking is a decidable process.
- **Formal Verification:** This computability makes type theory ideal for formalizing mathematics and verifying the correctness of computer programs. Proof assistants like Lean are built on type theory.
- **Expressiveness:** Type theory can express complex mathematical concepts in a natural and concise way.
- **Propositions as Types:** A key concept (to be explored later) is that propositions (statements that can be true or false) can also be treated as types. This creates a powerful connection between logic and computation.

### Applications

#### Computer Science

Type Theory has found extensive applications in computer science:

1.  **Programming Language Design**: Many modern programming languages incorporate ideas from Type Theory in their type systems.
2.  **Formal Verification**: Type Theory provides a basis for proving properties of programs and verifying their correctness.
3.  **Proof Assistants**: Software like Coq, Agda, and Lean, based on Type Theory, allow for computer-assisted theorem proving.
4.  **Foundations of Computer Science**: Type Theory provides a theoretical foundation for understanding computation and programming languages.

#### Mathematics

While Set Theory remains the most common foundation for mathematics, Type Theory offers some advantages:

1.  **Constructive Mathematics**: Type Theory naturally supports constructive approaches to mathematics.
2.  **Computational Content**: Proofs in Type Theory often have direct computational interpretations.
3.  **Higher-Order Logic**: Type Theory easily accommodates higher-order logic, which can be more expressive than first-order logic used in Set Theory.
4.  **Homotopy Type Theory**: Recent developments have connected Type Theory with modern areas of mathematics like homotopy theory.

---

[Universes and families](./Types.universe.html)
