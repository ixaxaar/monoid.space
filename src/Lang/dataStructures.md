---

[Contents](contents.html)
[Previous](Lang.naming.html)
[Next](Lang.functions.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

---

- [Data Structures](#data-structures)
  - [Introduction to Types in Agda](#introduction-to-types-in-agda)
    - [Declaring Types](#declaring-types)
    - [The `Set` Type](#the-set-type)
  - [Creating Custom Data Types with the `data` keyword](#creating-custom-data-types-with-the-data-keyword)
    - [Examples of Product Types](#examples-of-product-types)
    - [Examples of Sum Types](#examples-of-sum-types)
    - [Type Aliasing](#type-aliasing)
    - [Creating Custom Data Types in Haskell](#creating-custom-data-types-in-haskell)
    - [Creating Custom Data Types in Agda](#creating-custom-data-types-in-agda)
  - [Functions in Type Theory and Agda](#functions-in-type-theory-and-agda)
  - [Basic Types in Agda](#basic-types-in-agda)
    - [Empty Type](#empty-type)
    - [Unit Type](#unit-type)
    - [Boolean Type](#boolean-type)
    - [Natural Numbers](#natural-numbers)
  - [Lists](#lists)
  - [Binary Trees](#binary-trees)
  - [Graphs](#graphs)
  - [Vectors (Indexed Sequences)](#vectors-indexed-sequences)
  - [Finite Sets](#finite-sets)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Learning a new programming language usually consists of learning two basic things first:

1. Data structures and their APIs
2. Control logic (if/else, loops - for, while, do-while etc)

In a similar fashion, we take a look at how to construct familiar data structures first.

# Data Structures

```agda
module Lang.dataStructures where

open import Agda.Builtin.Nat public using (Nat; zero; suc)
open import Agda.Builtin.Bool public using (Bool; true; false)
```

## Introduction to Types in Agda

Agda is an implementation of type theory, a branch of mathematics that deals with `Type` as an object and various theorems (APIs) for working with `Type`s. A `Type` represents a notion of an object of a certain kind, meaning it assigns extra information to an object. If you are a programmer, you might already be familiar with the concept of `Type`, as its use is widespread in programming.

### Declaring Types

In type theory, we declare `A` as a type:

```haskell
A : Type
```

and say the object `x` is of type `A` like:

```scala
x : A
```

For example, in Scala, this is done like:

```scala
val x: Int = 0
```

In C:

```c
int x;
```

And in Agda:

```agda
variable
  x : Nat
  y : Nat
```

### The `Set` Type

The `Set` type is the type of types in Agda, somewhat akin to Java's `Object` or Scala's `Any`, but with important differences. Every other type is a `Set`, whereas `Set` itself is of type `Set₁`. This forms a hierarchy: `Set : Set₁ : Set₂ : ...` to avoid paradoxes. For most purposes, you can think of `Set` as meaning "type".

## Creating Custom Data Types with the `data` keyword

Programming languages often come with built-in primitive data types like `int`, `float`, `string`, etc., and some that combine these primitive types into more complex structures. Most languages allow creating new data types using either the product type (AND) or sum type (OR) on a set of pre-existing data types and enclosing them inside a container.

### Examples of Product Types

Consider the product of `String`, `Int`, and another `String`:

```scala
val a : (String, (Int, String)) = ...

val b : ((String, Int), String) = ...

val c : Map[String, (Int, String)] = ...
```

### Examples of Sum Types

```scala
val a : Option[A] = ... // Either A or null

val b : Either[A, B] = ... // Either type A or type B
```

### Type Aliasing

Some languages provide the mechanism to define new data types by aliasing a data type with a name, like in Scala:

```scala
type NewData = Map[String, List[Float]]
```

This is called type aliasing.

### Creating Custom Data Types in Haskell

Haskell provides the facility to define entirely new data types with the `data` keyword:

```haskell
data Bool = False | True

data Shape = Circle Float Float Float | Rectangle Float Float Float Float

-- Uses the Circle constructor to create an object of type Shape
myCircle = Circle 1.2 12.1 123.1

-- Uses the Rectangle constructor to create an object of type Shape
myRectangle = Rectangle 1.2 12.1 123.1 1234.5
```

### Creating Custom Data Types in Agda

The `data` keyword works in a similar manner in Agda:

```agda
data Shape : Set where
  Circle : Nat → Nat → Nat → Shape
  Rectangle : Nat → Nat → Nat → Nat → Shape
```

In this example, we define a custom `Shape` data type in Agda that can either be a `Circle` or a `Rectangle`. This is similar to how we defined the `Shape` data type in Haskell. We have defined these on natural numbers instead of real numbers. Later we will look at how insanely difficult it is to define real numbers in Agda (difficult enough that there are [research papers](https://ncatlab.org/nlab/files/Lundfall-RealNumbersInAgda.pdf) written on their implementation).

## Functions in Type Theory and Agda

In Type theory, a function `f` that operates on values of type `A` (domain of the function) and produces values of type `B` (co-domain of the function) is represented as:

f : A → B

A function in Agda consists of two main parts:

1. Types that the function operates on, including:
   1. Domain `Type`.
   2. Co-domain `Type`.
2. Clauses: each clause applies to a pattern of argument.

For example, here's a simple `not` function in Haskell:

```haskell
not : Bool → Bool
not True  = False
not False = True
```

This pattern-matching approach is typically found in functional programming languages and is used heavily in Agda.

## Basic Types in Agda

### Empty Type

An empty type cannot be created because it has no constructor:

```agda
data ⊥ : Set where
```

### Unit Type

A unit type contains only one object:

```agda
data ⊤ : Set where
  tt : ⊤
```

### Boolean Type

The boolean type has two values:

```agda
data Bool' : Set where
  true : Bool'
  false : Bool'
```

Note: we defined `Bool'` instead of `Bool` to avoid conflict with the stdlib imported above.

### Natural Numbers

Natural numbers are defined inductively:

```agda
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
```

We can define arithmetic operations on natural numbers:

```agda
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)
```

## Lists

Lists in Agda are defined inductively:

```agda
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_
```

We can create instances of lists as:

```agda
exampleList : List Bool
exampleList = true ∷ false ∷ true ∷ []
```

## Binary Trees

We can define binary trees in Agda:

```agda
data BinTree (A : Set) : Set where
  leaf : BinTree A
  node : A → BinTree A → BinTree A → BinTree A
```

## Graphs

We can represent graphs in Agda using vertices and edges:

```agda
data Vertex : Set where
  vertex : ℕ → Vertex

data Edge : Set where
  edge : Vertex → Vertex → Edge

data Graph : Set where
  emptyGraph : Graph
  addEdge : Graph → Edge → Graph
```

## Vectors (Indexed Sequences)

Vectors are lists with length information in the type:

```agda
data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)
```

Examples of vectors:

```agda
vec1 : Vec Bool 1
vec1 = true ∷ []

vec2 : Vec Bool 2
vec2 = false ∷ vec1
```

Note that each vector has its size encoded into its type. This is different from set theory-based lists, where any two lists of different numbers of elements have the same type.

## Finite Sets

A finite set can be considered as a finite bunch of numbered objects:

```agda
data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc : ∀ {n} → Fin n → Fin (suc n)
```

`Fin n` represents the set of the first n natural numbers, i.e., the set of all numbers smaller than n.

These data structures form the foundation for more complex structures and algorithms in Agda. As you become more comfortable with these concepts, you'll be able to define and work with increasingly sophisticated types and functions.

---

[Functions](./Lang.functions.html)
