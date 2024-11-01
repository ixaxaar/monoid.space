---

[Contents](contents.html)
[Previous](Lean.types.html)
[Next](Lean.other.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

---

- [Functions](#functions)
  - [Generic Syntax](#generic-syntax)
  - [Pattern matching functions](#pattern-matching-functions)
    - [Syntax](#syntax)
    - [The Logical Not](#the-logical-not)
    - [The logical AND](#the-logical-and)
    - [The logical OR](#the-logical-or)
    - [The logical XOR](#the-logical-xor)
  - [Recursive functions](#recursive-functions)
    - [Addition of natural numbers](#addition-of-natural-numbers)
    - [Length of a List](#length-of-a-list)
  - [Dependent Function Types](#dependent-function-types)
    - [Syntax](#syntax-1)
    - [Conditional Types](#conditional-types)
    - [Length-Indexed Vectors](#length-indexed-vectors)
    - [Working with Implicit Arguments](#working-with-implicit-arguments)
  - [Lambda Functions](#lambda-functions)
    - [Implicit Arguments: List concatenation](#implicit-arguments-list-concatenation)
    - [Dependent Pattern Matching: Square Root](#dependent-pattern-matching-square-root)
    - [Map](#map)
- [Syntactical Sugar](#syntactical-sugar)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Functions

[Contents](contents.md)
[Previous](Lean.types.md)
[Next](Lean.other.md)

Functions in Lean are defined using the `def` keyword. The syntax for defining functions in Lean is similar to defining inductive types.

These are the different types of functions we can define in Lean:

| Type of Function           | Description                                                   |
|----------------------------|---------------------------------------------------------------|
| Pattern-matching functions | Functions that match patterns to produce outputs              |
| Recursive functions        | Functions that call themselves to compute results             |
| Dependent functions        | Functions where the result type depends on the argument value |
| Lambda functions           | Anonymous functions that can be passed as arguments           |

Functions are also first-class citizens in Lean, meaning they can be passed as arguments to other functions, returned as results, and stored in data structures.

## Generic Syntax

Syntax for defining functions in Lean:

1. Define the name and type of the function using `def`
2. Define patterns and their corresponding outputs

```lean
-- 1. Name (not), Type (Bool → Bool)
def not : Bool → Bool
-- 2. Patterns and outputs
  | true  => false
  | false => true
```

## Pattern matching functions

Pattern-matching functions are functions that match patterns to produce outputs. They are defined using the `def` keyword, followed by the function name, type, and pattern-matching clauses.

### Syntax

The verbose lean syntax for pattern matching functions is:

```lean
def functionName : inputType → outputType
  match inputType with
    | pattern₁ => output₁
    | pattern₂ => output₂
    ...
    | patternN => outputN
```

This can be shortened to:

```lean
def functionName : inputType → outputType
  | pattern₁ => output₁
  | pattern₂ => output₂
  ...
  | patternN => outputN
```

There is also a version of pattern matching that uses a wildcard pattern (`_`) to match any value:

```lean
def functionName : inputType → outputType
  | pattern₁ => output₁
  | _        => defaultOutput
```

There are also infix functions, which are functions that can be used in infix notation. For example, the `and` function (`,`) can be used as `true ∧ false`.

```lean
def functionName : inputType → inputType → outputType
  | pattern₁, pattern₂ => output
  | pattern₃, pattern₄ => output
```

Finally, you can define functions with multiple arguments:

```lean
def functionName : inputType₁ → inputType₂ → outputType
  | pattern₁, pattern₂ => output
  | pattern₃, pattern₄ => output
```

### The Logical Not

The simplest of functions simply match patterns. For example, the function for `not`:

```lean
def not : Bool → Bool
  | true  => false -- return false if we are given a true
  | false => true  -- return a true if we are given a false
```

We could also use a wildcard pattern (`_`) like this:

```lean
def not₁ : Bool → Bool
  | true => false -- return false if we are given a true
  | _    => true  -- return true in all other cases
```

### The logical AND

In Lean, function names containing symbols can be used as infix operators. We can define precedence and associativity using `infix`, `infixl`, or `infixr`.

```lean
def and : Bool → Bool → Bool
  | true,  b => b     -- true AND whatever is whatever
  | false, _ => false -- false AND whatever is false

infixr:70 " ∧ " => and
```

We can use this function as:

```lean
def true₀ : Bool := true ∧ true
def false₀ : Bool := true ∧ false
```

### The logical OR

```lean
def or : Bool → Bool → Bool
  | true,  _ => true -- true or whatever is true
  | false, b => b    -- false or whatever is whatever

infixr:60 " ∨ " => or
```

These functions can be applied as:

```lean
def notTrue : Bool := not true

def false₁ : Bool := true ∧ false

def true₁ : Bool := true ∨ false ∨ false₁
```

### The logical XOR

The xor function with multiple arguments and wildcards:

```lean
def xor : Bool → Bool → Bool
  | true,  false => true  -- true XOR false is true
  | false, true  => true  -- false XOR true is true
  | _,     _     => false -- all other cases are false
```

## Recursive functions

Recursive functions are functions that call themselves to compute results. They are useful for defining functions that operate on recursive data structures or have recursive behavior.

The syntax for defining recursive functions in Lean is similar to pattern-matching functions, but with a recursive call to the function itself.

### Addition of natural numbers

The addition of natural numbers is a classic example of a recursive function. Here's how it can be defined in Lean:

```lean
def add : Nat → Nat → Nat
  | 0,    n => n -- base case: 0 + n is n
  | m+1,  n => (add m n) + 1 -- recursive case: (m+1) + n is m + (n+1)

infixl:65 " + " => add
```

### Length of a List

The length of a list consists of traversing through the list and adding one for each element:

```lean
def length {α : Type} : List α → Nat
  | []      => 0 -- base case: empty list has length 0
  | _ :: xs => 1 + length xs -- recursive case: 1 + length of the rest of the list
```

The `length` function takes a list of any type `α` and returns a natural number (`Nat`). It uses pattern matching to handle two cases:

1. If the list is empty (`[]`), the length is `0`.
2. If the list has at least one element (`_ :: xs`), the length is 1 plus the length of the rest of the list (`xs`).

This function recursively processes the list, accumulating the total count of elements until it reaches the empty list.

## Dependent Function Types

Dependent function types, also known as Π-types (Pi-types), represent one of the most powerful features in dependent type theory and Lean. Unlike simple function types where input and output types are fixed, dependent function types allow the *output type to depend on the input value*. This capability enables us to express complex relationships between values and types that would be impossible in simply-typed languages.

### Syntax

In Lean, dependent function types can be written in several ways:
- Using `Π` (Pi) notation
- Using `∀` (forall) notation
- Using arrow notation `→` when appropriate

Let's start with a simple example to illustrate the concept:

```lean
/-- A function that takes a type and returns a type.
    Note that even this simple example is a dependent type, as
    the result is a type that depends on the input type! -/
def F (α : Type) : Type := List α

/-
The type of F itself is Type → Type. This means it takes a type
and returns a type. While simple, this demonstrates the basic idea
of type dependency.
-/
#check F      -- Type → Type
#check F Nat  -- Type
```

### Conditional Types

One powerful application of dependent types is the ability to have different return types based on a condition. Here's an example:

```lean
/-- This function returns either a Nat or a String depending on the boolean input.
    Note how the return type uses an if-expression directly in the type! -/
def natOrStringThree (b : Bool) : if b then Nat else String :=
  match b with
  | true => (3 : Nat)
  | false => "three"
```

Let's examine what happens when we use this function:

```lean
#check natOrStringThree true   -- Nat
#check natOrStringThree false  -- String
#eval natOrStringThree true    -- 3
#eval natOrStringThree false   -- "three"
```

As we can see, the return type of `natOrStringThree` depends on the input value `b`. If `b` is `true`, the function returns a `Nat`, and if `b` is `false`, it returns a `String`.

### Length-Indexed Vectors

Perhaps the most classic example of dependent types is vectors - lists whose lengths are encoded in their types. This example showcases how dependent types can enforce properties at the type level:

A Vector is a list whose length is tracked in its type. α is the type of elements. The second parameter (Nat) indicates this is indexed by natural numbers:

```lean
inductive Vector (α : Type) : Nat → Type
  | nil  : Vector α 0                                        -- Empty vector has length 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n + 1)    -- Adding an element increases length by 1
```

Get the length of a vector. Note that we don't need to examine the vector itself, as the length is encoded in its type:

```lean
def vectorLength {α : Type} {n : Nat} (v : Vector α n) : Nat := n
```

Append two vectors. Notice how the return type shows that lengths add:

```lean
def append {α : Type} : {n m : Nat} → Vector α n → Vector α m → Vector α (n + m)
  | 0, m, Vector.nil, ys => ys
  | n+1, m, Vector.cons x xs, ys => Vector.cons x (append xs ys)
```

Let's create some vectors to see how this works:

```lean
def v1 := Vector.cons 1 Vector.nil           -- Vector Nat 1
def v2 := Vector.cons 2 (Vector.cons 3 Vector.nil)  -- Vector Nat 2
#check append v1 v2  -- Vector Nat 3
```

### Working with Implicit Arguments

Dependent types often work with implicit arguments, which Lean can infer from context. Consider a function that creates a vector of a specified length filled with a value:

```lean
-- Notice how {α : Type} is implicit but (n : Nat) is explicit
def replicate {α : Type} (n : Nat) (x : α) : Vector α n :=
  match n with
  | 0 => Vector.nil
  | n+1 => Vector.cons x (replicate n x)
```

Next, we define a `map` function that applies a function to each element of a vector:

```lean
def map {α β : Type} {n : Nat} (f : α → β) : Vector α n → Vector β n
  | Vector.nil => Vector.nil
  | Vector.cons x xs => Vector.cons (f x) (map f xs)
```

Let's see how these functions work:

```lean
#eval replicate 3 true   -- Vector of 3 trues
#check map (· + 1) (replicate 3 0)  -- Vector Nat 3
```

As we can see, the `replicate` function creates a vector of a specified length filled with a given value, and the `map` function applies a function to each element of a vector.

## Lambda Functions

Lambda (or anonymous) functions can be defined using the following syntax:

```lean
def example₁ := λ (α : Type) (x : α) => x
```

Here are a few examples of lambda functions:

### Implicit Arguments: List concatenation

Functions in Lean can work with implicit parameters, which means the compiler can infer certain argument values. For example:

```lean
def append {α : Type} : List α → List α → List α
  | [],    ys => ys
  | x::xs, ys => x :: append xs ys

infixr:65 " ++ " => append
```

Curly braces `{}` denote implicit arguments in Lean. Values of implicit arguments are derived from other argument values and types by solving type equations. You don't have to apply them explicitly (though they can be explicitly passed like `@function_name α`).

This function takes a type as a parameter `α`, and thus can work on `List`s of any type `α`. This feature of functions is called "parametric polymorphism".

### Dependent Pattern Matching: Square Root

Lean supports dependent pattern matching, which is similar to Agda's dot patterns. Here's an example:

```lean
inductive Square : Nat → Type where
  | sq : (m : Nat) → Square (m * m)

def root : (n : Nat) → Square n → Nat
  | _, Square.sq m => m
```

### Map

We implement the `map` function, of "map-reduce" fame, for `List`s:
A map function for a `List` is a function that applies a lambda (un-named) function to all elements of a `List`.

If `f` were a lambda function, mapping `f` over `List(a, b, c, d)` would produce `List(f(a), f(b), f(c), f(d))`

```lean
def map {α β : Type} : (α → β) → List α → List β
  | _, []      => []
  | f, x :: xs => f x :: map f xs
```

Here, we apply the function `addOne` to a list, using `map`:

```lean
def addOne : Nat → Nat
  | x => x + 1

#eval map addOne [1, 2, 3, 4]  -- Output: [2, 3, 4, 5]
```

# Syntactical Sugar

Lean provides syntactical sugar to simplify the expression of certain patterns:

```lean
-- (x : α) → (y : β) → γ  is equivalent to  (x : α) (y : β) → γ
-- ∀ (x : α), γ  is equivalent to  (x : α) → γ
-- ∀ x, γ  is equivalent to  (x : _) → γ  (type is inferred)
-- λ x y => e  is equivalent to  λ x => λ y => e
-- f a b  is equivalent to  (f a) b
```

---

[Modules, Structures, and Axioms](./Lean.other.md)

---

[Modules, Records and Postulates](./Lean.other.html)
