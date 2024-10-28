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
  - [Basic Types](#basic-types)
    - [Empty Type](#empty-type)
    - [Unit Type](#unit-type)
    - [Boolean Type](#boolean-type)
    - [Natural Numbers](#natural-numbers)
    - [Other Primitive Types](#other-primitive-types)
  - [Collections](#collections)
    - [Lists](#lists)
    - [Arrays](#arrays)
    - [Sets](#sets)
    - [Stacks](#stacks)
    - [Queues](#queues)
    - [Maps](#maps)
    - [Binary Trees](#binary-trees)
    - [Graphs](#graphs)
  - [Custom Data Types](#custom-data-types)
    - [Product Types](#product-types)
    - [Sum Types](#sum-types)
  - [Advanced Types](#advanced-types)
    - [Type Classes](#type-classes)
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

## Basic Types

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

### Other Primitive Types

| Type     | Description                                        | Example Usage               | Notes                                 |
|----------|----------------------------------------------------|-----------------------------|---------------------------------------|
| `Empty`  | The empty type with no values                      | `def f : Empty → α`         | Used for logical impossibility        |
| `Unit`   | The unit type with one value `unit`                | `def x : Unit := ()`        | Often used as dummy value             |
| `Bool`   | Booleans with values `true` and `false`            | `def b : Bool := true`      | Used for conditional logic            |
| `Nat`    | Natural numbers with zero and successor operations | `def n : Nat := 42`         | Non-negative integers (0, 1, 2, ...)  |
| `Int`    | Integers with addition, subtraction, etc.          | `def i : Int := -42`        | Whole numbers (positive and negative) |
| `Float`  | Floating-point numbers                             | `def f : Float := 3.14`     | IEEE 754 double-precision             |
| `String` | Strings                                            | `def s : String := "hello"` | UTF-8 encoded text                    |
| `Char`   | Single Unicode characters                          | `def c : Char := 'a'`       | Unicode code points                   |
| `USize`  | Platform-dependent unsigned integer                | `def u : USize := 42`       | Used for array indexing               |

## Collections

### Lists

Lean has built-in lists, similar to many functional programming languages:

```lean
inductive List (α : Type) : Type
  | nil  : List α                    -- Empty list
  | cons : α → List α → List α       -- Add element to front of list
```

This can be used to define, say, a list of booleans:

```lean
def exampleList : List Bool := [true, false, true]
```

Operations can be defined on lists, such as finding the length:

```lean
def length : List α → Nat
  | [] => 0
  | _::xs => 1 + length xs

#eval length exampleList  -- Output: 3
```

Lists are immutable, so operations like adding elements create new lists:

```lean
def exampleList2 := false :: exampleList
#eval length exampleList2  -- Output: 4
```

### Arrays

Dynamic arrays are also available in Lean, which are similar to lists but have better performance for some operations:

```lean
def exampleArray : Array Nat := #[1, 2, 3]
```

Here, `#[1,2,3]` is a shorthand for `Array.mk [1,2,3]`. We can access elements of the array using the `get!` function:

```lean
#eval exampleArray.get! 1  -- Output: 2
```

We can also use the `push` function to add elements to the array:

```lean
def exampleArray2 := exampleArray.push 4
#eval exampleArray2.get! 3  -- Output: 4
```

### Sets

Unordered sets can be implemented using the HashSet data structure. HashSets are data structures that store unique elements and provide fast lookup times. They are similar to sets in Python or Java.

```lean
import Std.Data.HashSet
open Std

-- create a set with elements 1, 2, 3
def exampleSet : HashSet Nat := HashSet.ofList [1, 2, 3]
```

```lean
#eval exampleSet.contains 2  -- true
#eval exampleSet.contains 4  -- false
```

Sets can be modified using functions like `insert` and `erase`:

```lean
def exampleSet2 := exampleSet.insert 4
#eval exampleSet2.contains 4  -- true
```

Finally, we can delete elements from the set using the `erase` function:

```lean
def exampleSet3 := exampleSet2.erase 4
#eval exampleSet3.contains 4  -- false
```

### Stacks

Stacks are a common data structure that follows the Last In First Out (LIFO) principle. We can implement a stack using a list:

```lean
structure Stack (α : Type) where
  elems : List α
deriving Repr
```

We can define operations like `push` and `pop` on the stack:

```lean
def push {α : Type} (s : Stack α) (x : α) : Stack α :=
  { s with elems := x :: s.elems } -- append x to the end of the list

-- in pop we return the top element and the rest of the stack
def pop {α : Type} (s : Stack α) : Option (α × Stack α) :=
  match s.elems with
  | [] => none
  | x :: xs => some (x, { elems := xs })
```

Here, `push` adds an element to the top of the stack, while `pop` removes and returns the top element:

```lean
def s : Stack Float := { elems := [1.0, 2.2, 0.3] }
def s' := push s 4.2
#eval pop s'  -- Output: some (4.200000, { elems := [1.000000, 2.200000, 0.300000] })
```

### Queues

Queues are another common data structure that follows the First In First Out (FIFO) principle. We can implement a queue using a list:

```lean
structure Q (α : Type) where
  elems : List α
deriving Repr

#eval x.elems  -- Output: [1, 2, 3]
```

Enqueue and dequeue operations can be performed on the queue:

```lean
def enqueue {α : Type} (q : Q α) (x : α) : Q α :=
  { q with elems := q.elems ++ [x] } -- append x to the end of the list

def dequeue {α : Type} (q : Q α) : Option (α × Q α) :=
  match q.elems with
  | [] => none
  | x :: xs => some (x, { elems := xs })
```

Finally, queues can be used as such:

```lean
def q : Q Float := { elems := [1.0, 2.2, 0.3] }
def q' := enqueue q 4.2
#eval dequeue q'  -- Output: some (1.000000, { elems := [2.200000, 0.300000, 4.200000] })
```

### Maps

Maps are key-value pairs that allow efficient lookup of values based on keys. These are similar to dictionaries in Python or hash maps in Java. We can implement a map using a list of key-value pairs:

```lean
structure Map (α β : Type) where
  pairs : List (α × β)
deriving Repr
```

We now need to define how to access elements in the map:

```lean
def find {α β : Type} [DecidableEq α] (m : Map α β) (key : α) : Option β :=
  match m.pairs.find? (fun (k, _) => k == key) with
  | some (_, v) => some v
  | none => none
```

Here, `find` searches for a key in the map and returns the corresponding value if found. We can define find as an infix operator for easier use:

```lean
infix:50 " ?? " => find
```

Here we define the `??` operator to find a value in the map. These are called as infix operators, and the number `50` is the precedence of the operator. This allows us to use the `??` operator to find values in the map:

```lean
def exampleMap1 : Map Nat String :=
  Map.mk [(1, "one"), (2, "two"), (3, "three")]

#eval exampleMap ?? 2  -- Output: some "two"
```

Representing maps as lists of key-value pairs is not the most efficient way to implement them, but it serves as a simple example. Lean also provides more efficient implementations of maps in the standard library.

We can use more optimized implementations by importing the `Std.Data.HashMap` module:

```lean
import Std.Data.HashMap
```

```lean
def exampleMap : Std.HashMap Nat String :=
  Std.HashMap.ofList [(1, "one"), (2, "two"), (3, "three")]

#eval exampleMap.contains 2  -- true
#eval exampleMap.get! 2  -- "two"
```

### Binary Trees

Binary trees are a common data structure in many languages. The data structure consists of nodes, each of which has a value and two children (left and right). Each node can be a leaf (no children) or an internal node (with children). We can define a binary tree in Lean as follows:

```lean
inductive BinTree (α : Type) : Type
  | leaf : BinTree α -- leaf node, with value of type α
  | node : α → BinTree α → BinTree α → BinTree α -- value, left child, right child
```

We can create a binary tree using the `leaf` and `node` constructors:

```lean
def exampleTree : BinTree Nat :=
  BinTree.node 1
    (BinTree.node 2 BinTree.leaf BinTree.leaf)
    (BinTree.node 3 BinTree.leaf BinTree.leaf)
```

This creates a binary tree with the following structure:

```
    1
   / \
  2   3
```

We can define operations on binary trees, such as finding the depth of the tree:

```lean
def depth : BinTree α → Nat
  | BinTree.leaf => 0
  | BinTree.node _ left right => 1 + max (depth left) (depth right)

#eval depth exampleTree  -- Output: 2
```

We will take a closer look on tree based algorithms in the next sections.

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

## Custom Data Types

Lean uses the `inductive` keyword to define new data types. This is similar to `data` in Haskell or `sealed class` in Kotlin.

### Product Types

Product types combine multiple values into a single type. They're similar to structs in C or dataclasses in Python.

```lean
structure Point where
  x : Float
  y : Float
```

This defines a new type `Point` with two fields `x` and `y`. We can create objects of this type using the constructor:

```lean
def myPoint : Point := { x := 1.0, y := 2.0 }
```

We can access the fields of the object using dot notation:

```lean
#eval myPoint.x  -- Output: 1.0
```

### Sum Types

Sum types (also known as tagged unions or algebraic data types) allow a value to be one of several types. They're similar to enums in Rust or union types in TypeScript.

```lean
inductive Shape
  -- constructor that takes in 3 floats and outputs an object of type Shape (a triangle)
  | triangle    : Float → Float → Float → Shape
  -- constructor that takes in 4 floats and outputs an object of type Shape (a rectangle)
  | rectangle : Float → Float → Float → Float → Shape
```

These constructors can be used to create objects of type `Shape`:

```lean
def myTriangle := Shape.triangle 1.2 12.1 123.1
def myRectangle := Shape.rectangle 1.2 12.1 123.1 1234.5
```

The `Shape` type can now be used in functions to calculate the area of a shape using pattern matching:

```lean
def area : Shape → Float
  | Shape.triangle _ _ r => Float.pi * r * r
  | Shape.rectangle _ _ w h => w * h
```

## Advanced Types

### Type Classes

Lean allows the definition of type classes, which are similar to interfaces in TypeScript or traits in Rust. They define a set of functions that a type must implement.

Lets take a very basic example, say we want all kinds of a certain type to have a zero value. We can define a type class `HasZero` that requires a zero value to be defined for any type that implements it:

```lean
-- Define a basic type class for types that have a "zero" value
class HasZero (α : Type) where
  zero : α  -- Every instance must provide a zero value
```

We can then implement this type class for different types:

```lean
-- Implement HasZero for some types
instance : HasZero Nat where
  zero := 0

instance : HasZero Bool where
  zero := false

instance : HasZero String where
  zero := ""
```

We can then use the `zero` function to get the zero value for any type that implements the `HasZero` type class:

```lean
-- Example usage
def getZero {α : Type} [HasZero α] : α := HasZero.zero

#eval getZero (α := Nat)    -- Output: 0
#eval getZero (α := Bool)   -- Output: false
#eval getZero (α := String)   -- Output: ""
```

A few more things to note here:

1. The curly braces `{}` are used to define type parameters. These are inferred by the compiler if not provided explicitly, for example, `getZero` can be defined as `def getZero [HasZero α] : α := HasZero.zero` and the compiler will infer the type `α` from the context.

2. The square brackets `[]` are used to define type class constraints. In this case, we require that the type `α` implements the `HasZero` type class. If the type does not implement the type class, the compiler will throw an error.

`getZero` is called a polymorphic function, as it can work with any type that implements the `HasZero` type class. Parametric polymorphism is a powerful feature of Lean that allows us to write generic functions that work with any type that satisfies certain constraints.

Here's another example of a `Plus` type class that defines a `plus` function which defines addition for all types that implement it:

```lean
class Plus (α : Type) where
  plus : α → α → α
```

This can be implemented for different types like `Nat` and `Float`:

```lean
instance : Plus Nat where
  plus := Nat.add

instance : Plus Float where
  plus := Float.add

instance : Plus String where
  plus := String.append
```

Finally, we can use the `plus` function on different types:

```lean
open Plus(plus)

#eval plus 4 5 -- 9
#eval plus 4.3 5.2 -- 9.500000
```

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
