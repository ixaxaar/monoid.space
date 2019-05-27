****
[Contents](contents.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Data Structures](#data-structures)
- [`Data` keyword](#data-keyword)
  - [Trivial types](#trivial-types)
    - [Empty](#empty)
    - [Singleton](#singleton)
  - [Boolean type](#boolean-type)
  - [Natural numbers](#natural-numbers)
  - [Binary Trees](#binary-trees)
  - [Graph](#graph)
  - [List](#list)
  - [Finite sequences](#finite-sequences)
  - [Indexed sequences or Vectors](#indexed-sequences-or-vectors)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Data Structures

Here we look at how to define data structures in Agda.

```agda
module Lang.dataStructures where
```

Agda is an implementation of type theory, a branch of mathematics where everything is a *type*. Unlike programming languages where there is a clear distinction betwen (data)type and data, where `1` is data of type `int`. In Agda, `1` is a type itself and is of type say `ℕ` (natural numbers). There do remain quite a few similarities, for example, like some programming languages allow functions to be passed around as objects of type `A => B`, similarly, all functions are also types in type theory. This simplicity could get confusing at first and takes some time to get used to given the reader has been a programmer for a while.

Just remember: in type theory, **EVERYTHING is a type**.

# `Data` keyword

As we probably know already, programming languages come bundled with some primitive data types like `int`, `float`, `string` etc and some that combine these primitive types into more complex structures, e.g. `map` can be used to construct say `map<string, array<string>>`.

Some languages also provide the mechanism to define new data types, sometimes by alias-ing a data type with a name like in scala:

```scala
type newData = Map[String, List[Float]]
```

This is called *type aliasing*.

Some languages provide the facility to define new data types, like haskell does with the `data` keyword:

```haskell
-- this states that the type `Bool` can have two values False and True
data Bool = False | True
```

A haskell datatype can also have constructors. For e.g. if we were to define a shape type which can either be a circle or a rectange:

```haskell
data Shape = Circle Float Float Float | Rectangle Float Float Float Float

-- uses the Circle constructor to create an object of type Shape
Circle 1.2 12.1 123.1

-- uses the Rectange constructor to create an object of type Shape
Rectange 1.2 12.1 123.1 1234.5
```

The `data` keyword works in a similar manner in Agda:

```agda
-- lets assume SomeType1 and SomeType2 to be previously defined
module _ {SomeType1 SomeType2 : Set} where

  data AgdaData : Set where
    -- constructors, all return AgdaData
    constructor1 : SomeType1 → AgdaData
    constructor2 : SomeType2 → AgdaData
    trivialConstructor : AgdaData
    etc : SomeType1 → SomeType2 → AgdaData
```

## Trivial types

### Empty

An empty object cannot be created cause it has no constructor. This is the most barebones of a `data` definition.

```agda
data ⊥ : Set where
```

### Singleton

A singleton is just a type containing only one object. Note that this is different from the singleton patterns prevalent in various languages like java.

```agda
data ⊤ : Set where
  singleton : ⊤
```

A singleton constructor `singleton` creates a single object of type `T`.

## Boolean type

The boolean type has just two values:

```agda
data Bool : Set where
  true : Bool
  false : Bool
```

## Natural numbers

All natural numbers can be created from `zero` and n successive numbers after `zero`. All we need to know are

- zero
- how to increment a number

and then, increment zero to infinity!

```agda
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
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

and so on recursively.

## Binary Trees

We define a generic complete binary tree using the following definition. Note that this merely creates an empty structure of a tree, the nodes or leaves contain no information in them:

![bintree](./bintree.png)

```agda
data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree
```

Now let us augment the binary trees with leaves containing natural numbers in leaf nodes:

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

Binary trees with each node containing a natural number and each leaf contaning a boolean:

```agda
data ℕMixedBinTree : Set where
  leaf : Bool → ℕMixedBinTree
  node : ℕ → ℕMixedBinTree → ℕMixedBinTree → ℕMixedBinTree
```

## Graph

![graph](./graph.png)

We define a graph with:

- edges containing a natural number
- represented as an edge-list, i.e. a list of triples

```agda
data Vertex : Set
data EdgeTriple : Set
data Graph : Set

data Vertex where
  vertex : ℕ → Vertex

data EdgeTriple where
  triple : Vertex → Vertex → EdgeTriple

data Graph where
  idGraph : EdgeTriple → Graph
  _+|+_ : Graph → EdgeTriple → Graph

infixl 3 _+|+_
```
The `infixl` sets the precedence of the infix operator `+|+`. To indicate an operator operates in an infix way, the operator `op` is represented as `_op_`. Similarly, for an operator `x + y = z`, we represent them as `_+_=_`.

We can use the above definition to create a graph in the following way:

```agda
graph : Graph
graph = idGraph (triple (vertex zero)   (vertex seven))     +|+
                triple  (vertex one)    (vertex three)      +|+
                triple  (vertex seven)  (vertex four)       +|+
                triple  (vertex nine)   (vertex (succ six))
```

## List

![list](./list.png)

A list containing objects of type `A` can be defined as an object which has:

- an identity element, i.e. an empty list `[]`
- a concat operator which successively creates bigger lists `::`

```agda
data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

infixr 5 _::_
```

and we create instances of lists as:

```agda
bunch : List Bool
bunch = false :: false :: true :: false :: true :: []
```

```agda
data TypeOf (A : Set) : Set where
  typeOf : List A → TypeOf A
```

```agda
nat : TypeOf ℕ
nat = typeOf ( one :: two :: ten :: [] )
```

## Finite sequences

The type class of a finite set, or merely an index, consists of:

- an identity element: create a finite set of size `n`
- a recursive creator: create finite sets successively

```agda
data Fin : ℕ → Set where
  id : (n : ℕ) → Fin (succ n)
  succ : (n : ℕ) → Fin n → Fin (succ n)
```

Creating a finite set of four elements:

```agda
fourFin : Fin four
fourFin = succ three (succ two (succ one (id zero)))
```

## Indexed sequences or Vectors

![vectors](./vector.png)

We now define a finite sized indexed list, also called a vector `Vec`. The constructor consists of:

- An identity constructor, `[]` which constructs an empty vector
- A successive constructor `cons` which appends successively builds a vector

```agda
data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  cons : (n : ℕ) → A → Vec A n → Vec A (succ n)
```

Examples of vectors :

```agda
vec1 : Vec Bool one
vec1 = cons zero true []

vec2 : Vec Bool two
vec2 = cons one false vec1

vec3 : Vec Bool three
vec3 = cons two true vec2
```

Note that each vector has its size encoded into it's type. This is not to be confused with set theory based lists, where any two list of different number of elements have the same type.

For example in scala:

```scala
val x : List[Int] = List(1,2,3,4,5)
val y : List[Int] = List(1,2,3,4,5,6,7,8,9,0)
```

both have the same type. However, in pure type theory they are considered different types as type theory considers the size of the list as type information.

Example, a bool-indexed vector such that only one type can be stored at the same time:

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

****
[Functions](./Lang.functions.html)
