---

[Contents](contents.html)
[Previous](Lang.naming.html)
[Next](Lang.functions.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

---

- [Setup and Installation for Lean](#setup-and-installation-for-lean)
- [Data Structures in Lean](#data-structures-in-lean)
  - [Introduction to Types in Lean](#introduction-to-types-in-lean)
    - [Declaring Types](#declaring-types)
    - [The `Type` Universe](#the-type-universe)
  - [Creating Custom Data Types](#creating-custom-data-types)
    - [Examples of Product and Sum Types](#examples-of-product-and-sum-types)
    - [Type Aliases](#type-aliases)
  - [Functions in Lean](#functions-in-lean)
  - [Basic Types in Lean](#basic-types-in-lean)
    - [Empty Type](#empty-type)
    - [Unit Type](#unit-type)
    - [Boolean Type](#boolean-type)
    - [Natural Numbers](#natural-numbers)
  - [Lists](#lists)
  - [Binary Trees](#binary-trees)
  - [Graphs](#graphs)
  - [Vectors (Sized Lists)](#vectors-sized-lists)
  - [Finite Sets](#finite-sets)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->
# Setup and Installation for Lean

[Previous content remains unchanged...]

# Data Structures in Lean

```lean
namespace DataStructures

import Init.Data.Nat
import Init.Data.List
import Init.Data.Fin
```

## Introduction to Types in Lean

Lean is based on dependent type theory, where types are first-class citizens. In Lean, types are objects of type `Type` or `Prop` (for propositions).

### Declaring Types

In Lean, we declare types like this:

```lean
def x : Nat := 0
def b : Bool := true
```

### The `Type` Universe

In Lean, `Type` is the type of types, similar to Agda's `Set`. Lean also has a hierarchy of type universes to avoid paradoxes: `Type`, `Type 1`, `Type 2`, etc.

## Creating Custom Data Types

Lean uses the `inductive` keyword to define new data types, which is similar to Agda's `data` keyword.

### Examples of Product and Sum Types

```lean
-- Product type (AND)
structure Point where
  x : Float
  y : Float

-- Sum type (OR)
inductive Shape
  | circle    : Float → Float → Float → Shape
  | rectangle : Float → Float → Float → Float → Shape

-- Using constructors
def myCircle := Shape.circle 1.2 12.1 123.1
def myRectangle := Shape.rectangle 1.2 12.1 123.1 1234.5
```

### Type Aliases

Lean allows type aliases using the `abbrev` keyword:

```lean
abbrev NewData := List Float
```

## Functions in Lean

In Lean, functions are defined using the `def` keyword:

```lean
def not : Bool → Bool
  | true  => false
  | false => true
```

## Basic Types in Lean

### Empty Type

```lean
inductive Empty : Type

-- There's also a predefined `Empty` type in Lean's standard library
```

### Unit Type

```lean
inductive Unit : Type
  | unit

-- Lean also has a predefined `Unit` type
```

### Boolean Type

```lean
-- Lean has a predefined Bool type, but here's how you could define it:
inductive Bool' : Type
  | true
  | false
```

### Natural Numbers

```lean
-- Lean has a predefined Nat type, but here's a simplified version:
inductive Nat' : Type
  | zero : Nat'
  | succ : Nat' → Nat'

-- Arithmetic operations
def add : Nat → Nat → Nat
  | 0,   n => n
  | m+1, n => (add m n) + 1

def mul : Nat → Nat → Nat
  | 0,   _ => 0
  | m+1, n => n + (mul m n)
```

## Lists

Lean has built-in lists, but here's how you could define them:

```lean
inductive List' (α : Type) : Type
  | nil  : List' α
  | cons : α → List' α → List' α

-- Example usage
def exampleList : List Bool := [true, false, true]
```

## Binary Trees

```lean
inductive BinTree (α : Type) : Type
  | leaf : BinTree α
  | node : α → BinTree α → BinTree α → BinTree α

-- Example usage
def exampleTree : BinTree Nat :=
  BinTree.node 1
    (BinTree.node 2 BinTree.leaf BinTree.leaf)
    (BinTree.node 3 BinTree.leaf BinTree.leaf)
```

## Graphs

We can represent graphs in Lean using vertices and edges:

```lean
inductive Vertex : Type
  | mk : Nat → Vertex

inductive Edge : Type
  | mk : Vertex → Vertex → Edge

inductive Graph : Type
  | empty : Graph
  | addEdge : Graph → Edge → Graph
```

## Vectors (Sized Lists)

Lean has a `Vector` type in its standard library, but here's a simplified version:

```lean
inductive Vector (α : Type) : Nat → Type
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

-- Example usage
def vec1 : Vector Bool 1 := Vector.cons true Vector.nil
def vec2 : Vector Bool 2 := Vector.cons false vec1
```

## Finite Sets

Lean's standard library includes a `Fin` type for finite sets:

```lean
-- Simplified version of Fin
inductive Fin' : Nat → Type
  | zero : {n : Nat} → Fin' (n+1)
  | succ : {n : Nat} → Fin' n → Fin' (n+1)
```

```lean
-- Example usage (using Fin from the library)
def fin0 : Fin 3 := Fin.ofNat 0
def fin1 : Fin 3 := Fin.ofNat 1
def fin2 : Fin 3 := Fin.ofNat 2
```

These data structures form the foundation for more complex structures and algorithms in Lean. As you become more comfortable with these concepts, you'll be able to define and work with increasingly sophisticated types and functions.

end DataStructures

---

[Functions](./Lang.functions.html)
