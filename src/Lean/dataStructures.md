---

[Contents](contents.html)
[Previous](Lang.naming.html)
[Next](Lang.functions.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

---

# Data Structures

---

- [Data Structures](#data-structures)
  - [Types](#types)
    - [Declaring Types](#declaring-types)
  - [Basic Types in Lean](#basic-types-in-lean)
    - [Empty Type](#empty-type)
    - [Unit Type](#unit-type)
    - [Boolean Type](#boolean-type)
    - [Natural Numbers](#natural-numbers)
  - [Creating Custom Data Types](#creating-custom-data-types)
    - [Product Types](#product-types)
    - [Sum Types](#sum-types)
    - [Type Aliases](#type-aliases)
  - [Common Data Structures](#common-data-structures)
    - [Lists](#lists)
    - [Binary Trees](#binary-trees)
    - [Graphs](#graphs)
  - [Advanced Types in Lean](#advanced-types-in-lean)
    - [Dependent Types](#dependent-types)
    - [Propositions as Types](#propositions-as-types)

## Types

In Lean, types are first-class citizens, meaning they can be manipulated and passed around just like any other value. This is similar to languages like Haskell or Scala, but with even more expressive as we shall see later.

### Declaring Types

In Lean, we declare types using the following syntax:

```lean
def x : Nat := 0
def b : Bool := true
```

This is similar to type annotations in languages like TypeScript or Kotlin.

## Basic Types in Lean

### Empty Type

The empty type, also known as the bottom type, is a type with no values. In some languages, this is called `Never` (TypeScript) or `Nothing` (Scala). This is a pre-defined type called `Empty` in Lean which is defined something as:

```lean
inductive Empty : Type
```

### Unit Type

The unit type is a type with exactly one value. This is similar to `void` in C++ or `()` in Haskell.

```lean
inductive Unit : Type
  | unit
```

Lean has a pre-defined unit type `Unit` which is defined like above.

### Boolean Type

Booleans are a fundamental type in most programming languages. In Lean, they're defined as:

```lean
inductive Bool : Type
  | false
  | true
```

This type can be used to define a function such as negation, which takes in a `Bool` and returns a `Bool`:

```lean
def negation (b : Bool) : Bool :=
  match b with -- an example of a switch-case in Lean
  | true => false -- if b is true, we return false
  | false => true -- if b is false, we return true
```

This is similar to boolean types in virtually all programming languages, but in Lean, we can prove properties about boolean operations using the type system. Let us see a proof of `negation (negation x) == x`:

```lean
theorem negationNegation (b : Bool) : negation (negation b) = b :=
  match b with
  | true => rfl
  | false => rfl

#check negationNegation
```

We will look at how to do stuff like this in later sections.

### Natural Numbers

Natural numbers are defined inductively in Lean:

```lean
inductive Nat : Type
  | zero : Nat -- define a zero object as the base
  | succ : Nat → Nat -- every such object has a succeeding object
```

Here, we define natural numbers by defining the element `zero` and the function `succ` that adds 1 to any given integer (creates the successive natural number) i.e. `succ zero` is 1, `succ (succ zero)` is two and so on. This is similar to Peano arithmetic and is foundational in type theory. In practice, `Nat` is a pre-defined type and Lean optimizes this to use machine integers for efficiency.

```lean
def one := succ zero
```

Arithmetic operations can now be defined on `Nat` like addition and multiplicattion:

```lean
def add : Nat → Nat → Nat
| zero, n => n
| m+one, n => (add m n) + one

def mul : Nat → Nat → Nat
| zero, _ => zero -- _ implies we dont care what the argument is
| m+one, n => n + (mul m n)
```

## Creating Custom Data Types

Lean uses the `inductive` keyword to define new data types. This is similar to `data` in Haskell or `sealed class` in Kotlin.

### Product Types

Product types combine multiple values into a single type. They're similar to structs in C or classes in Python.

```lean
structure Point where
  x : Float
  y : Float

-- Creating a point
def myPoint : Point := { x := 1.0, y := 2.0 }

-- Accessing fields
#eval myPoint.x  -- Output: 1.0
```

### Sum Types

Sum types (also known as tagged unions or algebraic data types) allow a value to be one of several types. They're similar to enums in Rust or union types in TypeScript.

```lean
inductive Shape
  | circle    : Float → Float → Float → Shape
  | rectangle : Float → Float → Float → Float → Shape

-- Using constructors
def myCircle := Shape.circle 1.2 12.1 123.1
def myRectangle := Shape.rectangle 1.2 12.1 123.1 1234.5

-- Pattern matching
def area : Shape → Float
  | Shape.circle _ _ r => Float.pi * r * r
  | Shape.rectangle _ _ w h => w * h
```

### Type Aliases

Lean allows type aliases using the `class` keyword, similar to `type` in TypeScript or `typealias` in Kotlin:

```lean
class Plus (α : Type) where
  plus : α → α → α

instance : Plus Nat where
  plus := Nat.add

instance : Plus Float where
  plus := Float.add

open Plus(plus)

#eval plus 4 5 -- 9
#eval plus 4.3 5.2 -- 9.500000
```

## Common Data Structures

### Lists

Lean has built-in lists, similar to many functional programming languages:

```lean
inductive List (α : Type) : Type
  | nil  : List α
  | cons : α → List α → List α

-- Example usage
def exampleList : List Bool := [true, false, true]

-- List operations
def length : List α → Nat
  | [] => 0
  | _::xs => 1 + length xs

#eval length exampleList  -- Output: 3
```

### Binary Trees

Binary trees are a common data structure in many languages:

```lean
inductive BinTree (α : Type) : Type
  | leaf : BinTree α
  | node : α → BinTree α → BinTree α → BinTree α

-- Example usage
def exampleTree : BinTree Nat :=
  BinTree.node 1
    (BinTree.node 2 BinTree.leaf BinTree.leaf)
    (BinTree.node 3 BinTree.leaf BinTree.leaf)

-- Tree operations
def depth : BinTree α → Nat
  | BinTree.leaf => 0
  | BinTree.node _ left right => 1 + max (depth left) (depth right)

#eval depth exampleTree  -- Output: 2
```

### Graphs

We can represent graphs in Lean using vertices and edges:

```lean
structure Vertex where
  id : Nat

structure Edge where
  from : Vertex
  to : Vertex

structure Graph where
  vertices : List Vertex
  edges : List Edge

-- Example usage
def v1 := Vertex.mk 1
def v2 := Vertex.mk 2
def e := Edge.mk v1 v2
def g : Graph := { vertices := [v1, v2], edges := [e] }
```

## Advanced Types in Lean

### Dependent Types

Dependent types are one of Lean's most powerful features. They allow types to depend on values:

```lean
-- Vector: a list with a statically known length
inductive Vector (α : Type) : Nat → Type
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

-- Example usage
def vec1 : Vector Bool 1 := Vector.cons true Vector.nil
def vec2 : Vector Bool 2 := Vector.cons false vec1

-- Type-safe head function
def head {α : Type} {n : Nat} : Vector α (n+1) → α
  | Vector.cons x _ => x

#eval head vec2  -- Output: false
-- This would be a compile-time error: #eval head Vector.nil
```

This is similar to dependent types in languages like Idris or Agda, but is not found in most mainstream programming languages.

### Propositions as Types

In Lean, propositions are types, and proofs are values of these types. This is known as the Curry-Howard correspondence:

```lean
-- Conjunction (AND)
def and_comm {p q : Prop} : p ∧ q → q ∧ p :=
  fun h => And.intro h.right h.left

-- Disjunction (OR)
def or_comm {p q : Prop} : p ∨ q → q ∨ p
  | Or.inl hp => Or.inr hp
  | Or.inr hq => Or.inl hq
```

This allows Lean to be used not just as a programming language, but as a powerful theorem prover.

---

[Functions](./Lang.functions.html)
