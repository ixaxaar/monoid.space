****
[Contents](contents.html)
[Previous](Lang.intro.html)
[Next](Lang.functions.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Data Structures](#data-structures)
  - [Introduction to Types in Agda](#introduction-to-types-in-agda)
    - [Declaring Types](#declaring-types)
    - [The `Set` Type](#the-set-type)
  - [Creating Custom Data Types with the `data` keyword](#creating-custom-data-types-with-the-data-keyword)
    - [Examples of Cartesian Product](#examples-of-cartesian-product)
    - [Examples of Cartesian Sum](#examples-of-cartesian-sum)
    - [Type Aliasing](#type-aliasing)
    - [Creating Custom Data Types in Haskell](#creating-custom-data-types-in-haskell)
    - [Creating Custom Data Types in Agda](#creating-custom-data-types-in-agda)
  - [Functions in Type Theory and Agda](#functions-in-type-theory-and-agda)
  - [Trivial Types in Agda](#trivial-types-in-agda)
    - [Empty Type](#empty-type)
    - [Singleton Type](#singleton-type)
  - [Boolean Type](#boolean-type)
  - [Natural Numbers](#natural-numbers)
  - [Binary Trees in Agda](#binary-trees-in-agda)
  - [Graph](#graph)
  - [List](#list)
  - [Finite set](#finite-set)
  - [Indexed sequences or Vectors](#indexed-sequences-or-vectors)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Learning a new programming language usually consists of learning two basic things first:
1. Data structures and their APIs
2. Control logic (if/else, loops - for, while, do-while etc)

In a similar fashion, we take a look at how to construct familiar data structures first.

# Data Structures

```agda
module Lang.dataStructures where

open import Agda.Builtin.Nat public using (Nat)
```

## Introduction to Types in Agda

Agda is an implementation of type theory, a branch of mathematics that deals with `Type` as an object and various theorems (APIs) for working with `Type`s. A `Type` represents a notion of an object of a certain kind, meaning it assigns extra information to an object. If you are a programmer, you might already be familiar with the concept of `Type`, as its use is widespread in programming.

### Declaring Types

In type theory, we declare `A` as a type:

```
A : Type
```

and say the object `x` is of type `A` like:

```
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
  x : ℕ
```

### The `Set` Type

The `Set` type is the root of all types in Agda, somewhat akin to Java's `Object` or Scala's `Any`. Every other type is a `Set`, whereas `Set` itself is of type `Set : Set₁`. We will explore this concept further later.


## Creating Custom Data Types with the `data` keyword

Programming languages often come with built-in primitive data types like `int`, `float`, `string`, etc., and some that combine these primitive types into more complex structures. For example, `map` or `dict` (in Python) can be used to construct structures like `map<string, array<string>>`, the `Either` data type in Haskell, the `Option` data type in Scala, `tuple` in Python, and so on.

Most languages allow creating new data types using either the cartesian product or cartesian sum (disjoint union) on a set of pre-existing data types and enclosing them inside a container.

### Examples of Cartesian Product

Consider the cartesian product of `String`, `Int`, and another `String`:

```scala
val a : Tuple2[String, Tuple2[Int, String]] = ...

val b : Tuple2[Tuple2[String, Int], String] = ...

val c : Map[String, (Int, String)] = ...
```

### Examples of Cartesian Sum

```scala
val a : Option[A] = ... // Either A or null

val a : Either[A, B] = ... // Either type A or type B
```

### Type Aliasing

Some languages provide the mechanism to define new data types, sometimes by aliasing a data type with a name, like in Scala:

```scala
type newData = Map[String, List[Float]]
```

This is called `type aliasing`.

### Creating Custom Data Types in Haskell

Other languages provide the facility to define entirely new data types, like Haskell does with the `data` keyword:

```haskell
-- This states that the type `Bool` can have two values False and True
data Bool = False | True
```

A Haskell data type can also have constructors. For example, if we were to define a shape type that can either be a circle or a rectangle:

```haskell
data Shape = Circle Float Float Float | Rectangle Float Float Float Float

-- Uses the Circle constructor to create an object of type Shape
Circle 1.2 12.1 123.1

-- Uses the Rectangle constructor to create an object of type Shape
Rectangle 1.2 12.1 123.1 1234.5
```

It is important to appreciate that `Shape` is a new `Type`, one that did not previously exist in the language.

### Creating Custom Data Types in Agda

The `data` keyword works in a similar manner in Agda:

```agda
-- Let's assume the type ℝ, or real numbers, is already defined
module _ {ℝ : Set} where
  data Shape : Set where
    Circle : ℝ → ℝ → ℝ → Shape
    Rectangle : ℝ → ℝ → ℝ → ℝ → Shape
```

In this example, we define a custom `Shape` data type in Agda that can either be a `Circle` or a `Rectangle`. This is similar to how we defined the `Shape` data type in Haskell. The `data` keyword in Agda allows you to create entirely new data types, just like in Haskell, providing you with more flexibility in your programming.

## Functions in Type Theory and Agda

In Type theory, a function `f` that operates on values of type `𝔸` (domain of the function) and produces values of type `𝔹` (co-domain of the function) is represented as:

$$
f : 𝔸 → 𝔹
$$

A function in Agda consists of two main parts:

1. Types that the function operates on, including:
   1. Domain `Type`.
   2. Co-domain `Type`.
2. Clauses: each clause applies to a pattern of argument.

For example, here's a simple `not` function in Haskell:

```haskell
not : Bool → Bool
not true  = false
not false = true
```

This pattern-matching approach is typically found in functional programming languages, and will be used heavily throughout this text. As Agda is implemented in Haskell and its syntax shares a high degree of similarity, it is helpful to be familiar with basic Haskell concepts.

## Trivial Types in Agda

### Empty Type

An empty type cannot be created because it has no constructor. This is the most basic `data` definition.

```agda
data ⊥ : Set where
```

### Singleton Type

A singleton type contains only one object:

```agda
data ⊤ : Set where
  singleton : ⊤
```

The `singleton` constructor creates a single object of type `⊤`.

## Boolean Type

The boolean type has two values:

```agda
data Bool : Set where
  true : Bool
  false : Bool
```

## Natural Numbers

Natural numbers are the positive integers used for counting (e.g., 0, 1, 2, 3...). Natural numbers support an operation called `succ` for succession, which can be used to create new natural numbers from known ones (e.g., `3 = 2 + 1 = 1 + 1 + 1`). Thus, all natural numbers can be created from `zero` and n successive numbers after `zero`. All we need to know are:

- zero
- how to increment a given number

Then, increment zero to infinity!

```agda
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
```

Operations for natural numbers, such as addition, subtraction, multiplication, and powers, can be defined as functions in Agda:

```agda
_+_ : ℕ → ℕ → ℕ
x + zero = x
x + (succ y) = succ (x + y)

_−_ : ℕ → ℕ → ℕ
zero  − m     = zero
succ n − zero  = succ n
succ n − succ m = n − m

_×_ : ℕ → ℕ → ℕ
x × zero     = zero
x × (succ y) = x + (x × y)

_² : ℕ → ℕ
x ² = x × x

_^_ : ℕ → ℕ → ℕ
x ^ zero = succ zero
x ^ (succ y) = x × (x ^ y)
```

Examples:

```agda
one   = succ zero
two   = succ one
three = succ two
four  = succ three
five  = succ four
six   = succ five
seven = succ six
eight = succ seven
nine  = succ eight
ten   = succ nine
```

Each member of the integer family can be derived from a smaller member by successively applying `succ`. Such a type is called an [**Inductive** type](https://en.wikipedia.org/wiki/Agda_(programming_language)#Inductivetypes).

Also note that in the function `_+_`, we used a new kind of clause:

```haskell
x + (succ y) = succ (x + y)
```

Here, we mean that for all inputs of the type `x + (succ y)` where `succ y` corresponds to a natural number that has been constructed using `succ` (i.e., `(succ y) > 0`), return `succ (x + y)`. This pattern is called "pattern matching". Pattern matching is heavily used throughout the functional programming world, such as in Scala:

```scala
(1 to 100).map{
  // pattern match against all values of type integer
  case(y:Int) if y > 5 =>
    y+1
  // if above pattern does not match
  case _ =>
    0
}
```

## Binary Trees in Agda

We define a binary tree using the following definition. Note that this merely creates an empty structure of a tree; the nodes or leaves contain no information in them, except for their position in the tree:

![Figure 1: Bintree](/artwork/bintree.png)

```agda
data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree
```

Now let's augment the binary trees with leaves containing natural numbers in leaf nodes:

```agda
data ℕBinTree : Set where
  leaf : ℕ → ℕBinTree
  node : ℕBinTree → ℕBinTree → ℕBinTree
```

Binary trees with each node and leaf containing a natural number:

```agda
data ℕNodeBinTree : Set where
  leaf : ℕ → ℕNodeBinTree
  node : ℕ → ℕNodeBinTree → ℕNodeBinTree → ℕNodeBinTree
```

Binary trees with each node containing a natural number and each leaf containing a boolean:

```agda
data ℕMixedBinTree : Set where
  leaf : Bool → ℕMixedBinTree
  node : ℕ → ℕMixedBinTree → ℕMixedBinTree → ℕMixedBinTree
```

## Graph

![Figure 2: Graph](/artwork/graph.png)

We define a graph with:

- Vertices containing a natural number
- Edges as triples containing `to` and `from` vertices

```agda
data Vertex : Set
data Edge   : Set
data Graph  : Set

data Vertex where
  vertex : ℕ → Vertex

data Edge where
  edge : Vertex → Vertex → Edge

data Graph where
  idGraph : Edge → Graph
  _+|+_ : Graph → Edge → Graph

infixl 3 _+|+_
```

Agda supports ["mixfix"](https://agda.readthedocs.io/en/v2.5.2/language/mixfix-operators.html) operators, which combine infix, prefix, and postfix operator semantics. Operator arguments are indicated with underscores `_`. An example would be the infix addition operator `_+_`, which, when applied with two parameters, can be written as `a + b`. Similarly, a prefix operator would be represented as `_♠`, a postfix one as `♠_`. It is also possible to define more complex operators like `if_then_else_`.

The `infixl` operator above sets the precedence of the operator `+|+`.

We can use the above definition to create a graph in the following way:

```agda
graph : Graph
graph = idGraph (edge (vertex zero)   (vertex seven))     +|+
                edge  (vertex one)    (vertex three)      +|+
                edge  (vertex seven)  (vertex four)       +|+
                edge  (vertex nine)   (vertex (succ six))
```

## List

![Figure 3: List](/artwork/list.png)

A list containing objects of type `A` can be defined inductively as having:

- An identity element, i.e., an empty list `[]`
- A concat operator which successively creates bigger lists `::`

```agda
data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

infixr 5 _::_
```

We create instances of lists as:

```agda
bunch : List Bool
bunch = false :: false :: true :: false :: true :: []
```

## Finite set

A finite set can be considered as a finite bunch of numbered objects, such that each object can be uniquely identified by an integer, thus making the set countable. This count is called the `Cardinality` of the set.

Formally, a finite set `Fin` is a set for which there exists a bijection (one-to-one and onto correspondence)

$$f : Fin → [n]$$

where $n ∈ ℕ$ and `[n]` is the set of all natural numbers from `0` to `n`.

This can be represented in Agda as:

```agda
data Fin : ℕ → Set where
  id : (n : ℕ) → Fin (succ n)
  succ : (n : ℕ) → Fin n → Fin (succ n)
```

`Fin n` represents the set of the first n natural numbers, i.e., the set of all numbers smaller than n. We create a finite set of four elements:

```agda
fourFin : Fin four
fourFin = succ three (succ two (succ one (id zero)))
```

For a more in-depth treatment of finite sets, refer to [Dependently Typed Programming with Finite Sets](http://firsov.ee/finset/finset.pdf).

## Indexed sequences or Vectors

![Figure 4: Vectors](/artwork/vector.png)

We now define a finite sized indexed list, also called a vector `Vec`. The constructor consists of:

- An identity constructor, `[]`, which constructs an empty vector
- A successive constructor `cons`, which inductively builds a vector

```agda
data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  cons : (n : ℕ) → A → Vec A n → Vec A (succ n)
```

Examples of vectors:

```agda
vec1 : Vec Bool one
vec1 = cons zero true []

vec2 : Vec Bool two
vec2 = cons one false vec1

vec3 : Vec Bool three
vec3 = cons two true vec2
```

Note that each vector has its size encoded into its type. This is not to be confused with set theory-based lists, where any two lists of different numbers of elements have the same type.

For example:

```scala
val x : List[Int] = List(1,2,3,4,5)
val y : List[Int] = List(1,2,3,4,5,6,7,8,9,0)
```

Both have the same type `List[Int]`.

Another example:

A bool-indexed vector such that only one type can be stored at the same time:

```agda
data ⟂ : Set where

data BoolVec(A B : Set) : Bool → Set where
  id₁ : B → BoolVec A B false
  id₂ : A → BoolVec A B true

containsB : BoolVec ⟂ ℕ false
containsB = id₁ three

containsA : BoolVec ℕ ⟂ true
containsA = id₂ four
```

[Functions](./Lang.functions.html)