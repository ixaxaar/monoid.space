<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Data Structures](#data-structures)
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

```agda
module Lang.dataStructures where
```

## Trivial types

### Empty

```agda
data ⊥ : Set where
```

An empty object cannot be created cause it has no constructor.

### Singleton

```agda
data ⊤ : Set where
  singleton : ⊤
```

A singleton constructor `singleton` creates a single object of type `T`.

## Boolean type

```agda
data Bool : Set where
  true : Bool
  false : Bool
```

Here `data Bool` represents a data type creator Bool, which contains two type constructors, `true` and `false`. Each consructor here, `true` and `false` returns a `Bool` value, this is represented as `true : Bool`. Notice that the data type constructor itself is a menber of `Set`. There can be ones that depend on others though we know a about them in type theory.

## Natural numbers

```agda
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
```

All natural numbers can be created from `zero` and n successive numbers after `zero`. All we need to know are

- zero
- how to increment a number

and then, increment zero to infinity!

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

```agda
data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree
```

Binary trees with leaves containing natural numbers in leaf nodes:

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
[Back to Contents](./contents.html)
