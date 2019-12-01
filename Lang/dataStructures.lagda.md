****
[Contents](contents.html)
[Previous](Lang.intro.html)
[Next](Lang.functions.html)

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
  - [Finite set](#finite-set)
  - [Indexed sequences or Vectors](#indexed-sequences-or-vectors)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Data Structures

Here we look at how to define data structures in Agda.

```agda
module Lang.dataStructures where
```

Agda is an implementation of type theory, a branch of mathematics. A type presents a notion of an object belonging to a certain characteristic, it assigns some extra information to an object.

To declare `A` as a type:

$$
A : Type
$$

or in Agda:

```agda
module _ {A : Set} where
```

We say the object `x` is of type `A` like:

$$
x : A
$$

# `Data` keyword

Programming languages often come bundled with some primitive data types like `int`, `float`, `string` etc and some that combine these primitive types into more complex structures, e.g. `map` can be used to construct say `map<string, array<string>>` or the `Either` datatype in haskell, the `Option` datatype in scala and so on.

Some languages also provide the mechanism to define new data types, sometimes by alias-ing a data type with a name like in scala:

```scala
type newData = Map[String, List[Float]]
```

This is called *type aliasing*.

Others provide the facility to define new data types, like haskell does with the `data` keyword:

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

An empty type cannot be created cause it has no constructor. This is the most barebones of a `data` definition.

```agda
data ⊥ : Set where
```

### Singleton

A singleton is just a type containing only one object:

```agda
data ⊤ : Set where
  singleton : ⊤
```

The singleton constructor `singleton` creates a single object of type `T`.

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

The operations for natual numbers, addition, subtraction, multiplication and powers can be defined as functions in Agda:

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

and so on. Here, each member of the integer family can be derived from a smaller member by successively applying `succ` to it. Such a type is called an [**Inductive** type](https://en.wikipedia.org/wiki/Agda_(programming_language)#Inductive_types).

## Binary Trees

We define a binary tree using the following definition. Note that this merely creates an empty structure of a tree, the nodes or leaves contain no information in them, except for their position in the tree:

![Figure 1: Bintree](./bintree.png)

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

![Figure 2: Graph](./graph.png)

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

Agda supports ["mixfix"](https://agda.readthedocs.io/en/v2.5.2/language/mixfix-operators.html) operators which combine infix, prefix and postfix operator semantics. Operator arguments are indicated with underscores `_`. An example would be the infix addition operator `_+_` which when applied with two parameters can be written as `a + b`. Similarly, a prefix operator would be represented as `♠_`, a postfix one as `♠_`. It is also possible to define more complex operators like `if_then_else_`.

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

![Figure 3: List](./list.png)

A list containing objects of type `A` can be defined inductively as having:

- An identity element, i.e. an empty list `[]`
- A concat operator which successively creates bigger lists `::`

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

## Finite set

A finite set can be considered as a finite bunch of numbered objects, such that each object can be uniquely identified by an integer. Formally, a finite set `Fin` is a set for which there exists a bijection (one-to-one and onto correspondence) $f : Fin → [n]$ where $n ∈ ℕ$ and `[n]` is the set of all natural numbers from `0` to `n`.

```agda
data Fin : ℕ → Set where
  id : (n : ℕ) → Fin (succ n)
  succ : (n : ℕ) → Fin n → Fin (succ n)
```

`Fin n` represents the set of first n natural numbers, i.e., the set of all numbers smaller than n. We create a finite set of four elements:

```agda
fourFin : Fin four
fourFin = succ three (succ two (succ one (id zero)))
```

For a more in-depth treatment of finite sets, refer [Dependently Typed Programming with Finite Sets](http://firsov.ee/finset/finset.pdf).

## Indexed sequences or Vectors

![Figure 4: Vectors](./vector.png)

We now define a finite sized indexed list, also called a vector `Vec`. The constructor consists of:

- An identity constructor, `[]` which constructs an empty vector
- A successive constructor `cons` which inductively builds a vector

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

For example:

```scala
val x : List[Int] = List(1,2,3,4,5)
val y : List[Int] = List(1,2,3,4,5,6,7,8,9,0)
```

both have the same type `List[Int]`.

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
