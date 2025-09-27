---

[Contents](contents.html)
[Previous](Lean.naming.html)
[Next](Lean.functions.html)

# Types & Data Structures

---

- [Types](#types)
  - [Declarations](#declarations)
  - [Lean Syntax](#lean-syntax)
  - [Basic Declarations](#basic-declarations)
  - [The `inductive` Keyword](#the-inductive-keyword)
  - [The `structure` Keyword](#the-structure-keyword)
  - [The `deriving` Clause](#the-deriving-clause)
  - [Type Inference](#type-inference)
  - [Immutability](#immutability)
  - [Variable scope](#variable-scope)
- [Basic Types](#basic-types)
  - [Empty Type](#empty-type)
  - [Unit](#unit)
  - [Boolean](#boolean)
  - [Natural Numbers](#natural-numbers)
  - [Characters and Strings](#characters-and-strings)
    - [Characters](#characters)
    - [Strings](#strings)
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
- [Custom Types](#custom-types)
  - [Product Types](#product-types)
  - [Sum Types](#sum-types)
- [Advanced Types](#advanced-types)
  - [Type Classes](#type-classes)
  - [Dependent Types](#dependent-types)

## Types

In Lean, types are first-class citizens, meaning they can be manipulated and passed around just like any other value. This is similar to functional programming languages like Haskell or Scala, but with even more expressiveness as we shall see later.

### Declarations

In Lean, we declare variables with type annotations using the following syntax:

```lean
def x : Nat := 0
def b : Bool := true
```

This is similar to type annotations in languages like TypeScript or Kotlin. The `def` keyword is used to define a new variable, `x`, with type `Nat` and value `0`. Similarly, `b` is defined as a `Bool` with value `true`. The types `Nat` and `Bool` are built-in types in Lean, representing natural numbers and boolean values, respectively.

### Lean Syntax

Before we dive further into types, here are a few of Lean's syntax elements that will be useful:

**Keywords:**

| Keyword     | Purpose                                                         |
| ----------- | --------------------------------------------------------------- |
| `def`       | Defines functions and values                                    |
| `inductive` | Defines algebraic data types                                    |
| `structure` | Defines record types (product types)                            |
| `where`     | Introduces definitions or constraints                           |
| `deriving`  | Automatically generates implementations for common type classes |
| `open`      | Brings namespace contents into scope                            |

**Argument types:**

| Argument Type   | Description                          | Example                        |
| --------------- | ------------------------------------ | ------------------------------ |
| `(x : Type)`    | Explicit arguments, must be provided | `def f (n : Nat) : Nat`        |
| `{x : Type}`    | Implicit arguments, inferred by Lean | `def f {α : Type} (x : α) : α` |
| `[TypeClass α]` | Type class constraints               | `def f [Add α] (x y : α) : α`  |

**Operators:**

| Operator | Description                                 | Example                                     |
| -------- | ------------------------------------------- | ------------------------------------------- |
| `::`     | List cons (prepend element)                 | `1 :: [2, 3]` results in `[1, 2, 3]`        |
| `++`     | String/list concatenation                   | `"hello" ++ " world"` or `[1, 2] ++ [3, 4]` |
| `\|`     | Pattern matching cases or type constructors | `\| some x => x` or `\| nil \| cons`        |

### Basic Declarations

To define values of a certain type, we can use the `def` keyword followed by the variable name, a colon, the type, an equals sign, and the value. For example:

```lean
def myNumber : Nat := 42
def myBoolean : Bool := true
def myString : String := "Hello, Lean!"
```

Here, `myNumber` is defined as a natural number (`Nat`) with the value `42`, `myBoolean` is a boolean (`Bool`) with the value `true`, and `myString` is a string (`String`) with the value `"Hello, Lean!"`.

### The `inductive` Keyword

The `inductive` keyword is used to define new types in Lean. It is similar to `data` in Haskell or `sealed class` in Kotlin. Its syntax is as follows:

```lean
inductive TypeName (type parameters) : Type
  | constructor1 : Type1 → TypeName
  | constructor2 : Type2 → TypeName
  ...
```

Here, `TypeName` is the name of the new type being defined, and it can take type parameters (like generics in other languages). The `: Type` part indicates that `TypeName` is a type. Each constructor defines a way to create values of this type, with their respective types. We will see some examples below.

### The `structure` Keyword

The `structure` keyword defines product types (records) - types that combine multiple fields:

```lean
structure StructName (parameters) where
  field1 : Type1
  field2 : Type2
```

This is similar to `struct` in C++ or classes with only data fields in other languages.

### The `deriving` Clause

The `deriving` clause can be used with `inductive` and `structure` to automatically generate implementations for common type classes. This is similar to `deriving` in Haskell or `@dataclass` in Python. For example, we can derive `Repr`, `BEq`, and `Hashable` for a `Point` structure like so:

```lean
structure Point where
  x : Float
  y : Float
deriving Repr, BEq, Hashable
```

Common derivable type classes include:

- `Repr` - enables printing values with `#eval`
- `BEq` - enables equality comparison with `==`
- `Hashable` - enables use in hash tables
- `Inhabited` - provides a default value

### Type Inference

Lean can infer types automatically in many cases, so explicit type annotations are often optional. For example:

```lean
def myNumber := 42          -- Lean infers Nat
def myBoolean := true       -- Lean infers Bool
def myString := "Hello!"    -- Lean infers String
def myList := [1, 2, 3]     -- Lean infers List Nat
```

However, providing explicit types can improve code clarity and help catch errors early.

### Immutability

All values in Lean are immutable by default. This means that once a value is assigned, it cannot be changed. This is similar to `val` in Kotlin or `final` in Java. If a value is reassigned, it results in a compile-time error. For example:

```lean
def x : Nat := 10
-- x := 20  -- This would be a compile-time error
```

### Variable scope

Variables defined with `def` have global scope within the module they are defined in. To create local variables, you can use `let` within functions or blocks:

```lean
let y := 5 in
let z := y + 10 in
z  -- z is 15
```

## Basic Types

There are several primitive types in Lean, let's have a look:

### Empty Type

The empty type, also known as the bottom type, is a type with no values. In some languages, this is called `Never` (TypeScript) or `Nothing` (Scala). This is a pre-defined type called `Empty` in Lean which is defined as:

```lean
inductive Empty : Type
```

An empty type is useful in situations where a function should never return, such as in the case of a function that always throws an error or enters an infinite loop. Note that this is unlike `void` in languages like C or Java, which represents the absence of a value but still allows functions to return.

### Unit

The unit type is a type with exactly one value. This is similar to `void` in C++ or `()` in Haskell.

```lean
inductive Unit : Type
  | unit
```

Lean has a pre-defined unit type `Unit` which is defined like above.

### Boolean

Booleans are a fundamental type in most programming languages. In Lean, they're defined as:

```lean
inductive Bool : Type
  | false
  | true
```

Note that it is always possible to define your own boolean type, but it's generally not recommended as the type also comes with a lot of built-in functionality. Here is how to do that:

```lean
inductive Status : Type
  | affirmative
  | negative
```

### Natural Numbers

Natural numbers, or non-negative integers (0, 1, 2, ...), are generally represented using Peano arithmetic in type theory, where:

1. One starts with a base case (0).
2. A successor function `succ` which takes a natural number `n` and returns `n + 1`.

Thus, there are two constructors: `zero` for 0, and `succ` for the successor function. This is defined inductively in Lean as follows:

```lean
inductive Nat : Type
  | zero : Nat -- define a zero object as the base
  | succ : Nat → Nat -- every such object has a succeeding object
```

Using these constructors, we can define natural numbers like so:

```lean
def one := succ zero
```

Lean has support for built-in natural numbers `Nat` as well as integer literals, so we can simply write:

```lean
def two : Nat := 2
def three : Nat := 3
```

Here `2` and `3` are syntactic sugar for `succ (succ zero)` and `succ (succ (succ zero))`, respectively.

Lean provides the standard arithmetic operations on natural numbers, such as addition, subtraction, multiplication, and exponentiation. For example:

```lean
def five : Nat := 2 + three
def six : Nat := 2 * three
def eight : Nat := 2 ^ three  -- 2 raised to the power of 3
```

### Characters and Strings

Lean has a `Char` type for single Unicode characters and a `String` type for sequences of characters. In computing systems, characters are often represented as integers corresponding to their Unicode code points e.g., the character 'A' has a Unicode code point of `65` or `0x41` in hexadecimal.

#### Characters

The `Char` type in Lean represents Unicode characters and is defined as:

```lean
inductive Char : Type
  | mk : UInt32 → Char  -- Unicode code point
```

You can work with characters using character literals:

```lean
def letterA : Char := 'A'
def emoji : Char := '🎉'
def newline : Char := '\n'
```

#### Strings

Strings in Lean are sequences of characters, implemented efficiently as UTF-8 encoded byte arrays. You can create and work with strings like this:

```lean
def greeting : String := "Hello, World!"
def multiline : String := "Line 1\nLine 2"
def unicode : String := "café 🌟"
```

Common string operations include:

```lean
def length := greeting.length         -- Get string length
def isEmpty := "".isEmpty             -- Check if empty
def concat := "Hello" ++ " World"     -- String concatenation
def charAt := greeting.get! 0         -- Get character at index
```

Strings support interpolation using the `s!` syntax:

```lean
def name := "Alice"
def age := 30
def message := s!"Hello {name}, you are {age} years old"
```

### Other Primitive Types

| Type     | Description                                        | Example Usage               | Notes                                 |
| -------- | -------------------------------------------------- | --------------------------- | ------------------------------------- |
| `Empty`  | The empty type with no values                      | `def f : Empty → α`         | Used for logical impossibility        |
| `Unit`   | The unit type with one value `unit`                | `def x : Unit := ()`        | Often used as dummy value             |
| `Bool`   | Booleans with values `true` and `false`            | `def b : Bool := true`      | Used for conditional logic            |
| `Nat`    | Natural numbers with zero and successor operations | `def n : Nat := 42`         | Non-negative integers (0, 1, 2, ...)  |
| `Int`    | Integers with addition, subtraction, etc.          | `def i : Int := -42`        | Whole numbers (positive and negative) |
| `Float`  | Floating-point numbers                             | `def f : Float := 3.14`     | IEEE 754 double-precision             |
| `String` | Strings                                            | `def s : String := "hello"` | UTF-8 encoded text                    |
| `Char`   | Single Unicode characters                          | `def c : Char := 'a'`       | Unicode code points                   |
| `USize`  | Platform-dependent unsigned integer                | `def u : USize := 42`       | Used for array indexing               |
| `UInt8`  | 8-bit unsigned integer                             | `def u8 : UInt8 := 255`     | Range 0-255                           |
| `UInt16` | 16-bit unsigned integer                            | `def u16 : UInt16 := 65535` | Range 0-65535                         |
| `UInt32` | 32-bit unsigned integer                            | `def u32 : UInt32 := 42`    | Range 0-4294967295                    |
| `UInt64` | 64-bit unsigned integer                            | `def u64 : UInt64 := 42`    | Range 0-18446744073709551615          |
| `Prop`   | The type of propositions                           | `def p : Prop := True`      | Used in theorem proving               |
| `Type`   | The type of types                                  | `def T : Type := Nat`       | Universe level 0                      |
| `Sort`   | Generic universe type                              | `def S : Sort u := Type`    | Encompasses Type and Prop             |

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

-- create a set with elements 1, 2, 3
def exampleSet : Std.HashSet Nat := Std.HashSet.ofList [1, 2, 3]
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

Here we use the `structure` keyword to define a new data structure `Stack` with a single field `elems` of type `List α`. To actually define the behavior of the stack, we also need to define the push and pop operations which we cover in the next chapter on functions.

### Queues

Queues are another common data structure that follows the First In First Out (FIFO) principle. We can implement a queue using a list:

```lean
structure Queue (α : Type) where
  elems : List α
deriving Repr
```

### Maps

Maps are key-value pairs that allow efficient lookup of values based on keys. These are similar to dictionaries in Python or hash maps in Java. We can implement a simple map using a list of key-value pairs:

```lean
structure Map (α β : Type) where
  pairs : List (α × β)
deriving Repr
```

For more efficient implementations, Lean provides `Std.HashMap` in the standard library which can be used as follows:

```lean
import Std.Data.HashMap
def exampleMap : Std.HashMap String Nat := Std.HashMap.empty.insert "one" 1 |>.insert "two" 2
```

### Binary Trees

Binary trees are a common data structure in many languages. The data structure consists of nodes, each of which has a value and two children (left and right). Each node can be a leaf (no children) or an internal node (with children). We can define a binary tree in Lean as follows:

```lean
inductive BinTree (α : Type) : Type
  | leaf : BinTree α -- leaf node with no value
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

```bash
    1
   / \
  2   3
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
```

Here, we define a `Vertex` as a structure with an `id` field, an `Edge` as a structure with `from` and `to` fields, and a `Graph` as a structure with lists of vertices and edges. We can create vertices and edges and define a graph as follows:

```lean
def v1 := Vertex.mk 1
def v2 := Vertex.mk 2
def e := Edge.mk v1 v2
def g : Graph := { vertices := [v1, v2], edges := [e] }
```

## Custom Types

There are two main ways to define custom types in Lean: product types and sum types.

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
  -- constructor that takes in a radius and outputs a circle
  | circle    : Float → Shape
  -- constructor that takes in width and height and outputs a rectangle
  | rectangle : Float → Float → Shape
```

These constructors can be used to create objects of type `Shape`:

```lean
def myCircle := Shape.circle 5.0
def myRectangle := Shape.rectangle 4.0 6.0
```

`Option` and `Either` types are also examples of sum types:

```lean
inductive Option (α : Type) : Type
  | none : Option α
  | some : α → Option α

inductive Either (α β : Type) : Type
  | left  : α → Either α β
  | right : β → Either α β
```

## Advanced Types

### Type Classes

Type classes allow for ad-hoc polymorphism, enabling functions to operate on different types based on the capabilities those types provide. A typeclass defines a set of functions that a type must implement to be considered an instance of that class. This is similar to interfaces in languages like TypeScript or traits in Rust.

Lets take a very basic example, say we want all kinds of a certain type to have a zero value. We can define a type class `HasZero` that requires a zero value to be defined for any type that implements it:

```lean
-- Define a basic type class for types that have a "zero" value
class HasZero (α : Type) where
  zero : α  -- Every instance must provide a zero value
```

Any type that implements the `HasZero` type class must provide a `zero` value. This property can be implemented for different types like `Nat`, `Bool`, and `String`:

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
#eval HasZero.zero (α := Nat)      -- Output: 0
#eval HasZero.zero (α := Bool)     -- Output: false
#eval HasZero.zero (α := String)   -- Output: ""
```

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

#eval plus 4 5         -- 9
#eval plus 4.3 5.2     -- 9.500000
```

Note the `open Plus(plus)` line, which brings the `plus` function into scope so we can use it without prefixing it with `Plus.`. Instead we could also use `Plus.plus` directly.

### Dependent Types

Dependent types are one of Lean's most powerful features. They allow types to depend on values:

```lean
-- Vector: a list with a statically known length
inductive Vector (α : Type) : Nat → Type
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
```

Here, `Vector α n` is a vector of length `n` containing elements of type `α`. The `nil` constructor creates an empty vector, while the `cons` constructor adds an element to the front of a vector. The length of the vector is encoded in the type itself, so the type system ensures that operations like `head` (which returns the first element of a non-empty vector) are safe:

```lean
def vec1 : Vector Bool 1 := Vector.cons true Vector.nil
def vec2 : Vector Bool 2 := Vector.cons false vec1

-- This would be a compile-time error: head Vector.nil as it has length 0
```

This is similar to dependent types in languages like Idris or Agda, but is not found in most mainstream programming languages. Dependent types allow us to encode complex invariants in the type system, leading to safer and more expressive code, and moving some runtime errors to compile-time errors.

---

[Functions](./Lean.functions.html)
