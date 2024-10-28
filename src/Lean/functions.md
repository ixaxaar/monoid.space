---

[Contents](contents.html)
[Previous](Lean.types.html)
[Next](Lean.other.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

---

- [Functions](#functions)
  - [Generic Syntax](#generic-syntax)
  - [Examples - Pattern matching functions](#examples---pattern-matching-functions)
    - [The Logical Not](#the-logical-not)
    - [The logical AND](#the-logical-and)
    - [The logical OR](#the-logical-or)
  - [Examples - Recursive functions](#examples---recursive-functions)
    - [Addition of natural numbers](#addition-of-natural-numbers)
    - [Length of a List](#length-of-a-list)
- [Dependent Function Types or Π-types](#dependent-function-types-or-π-types)
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

## Examples - Pattern matching functions

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

## Examples - Recursive functions

### Addition of natural numbers

Here we follow a similar pattern as in `inductive`, we define:

- the base case, what happens on addition with zero
- and how to successively build up the final value

```lean
def add : Nat → Nat → Nat
  | 0,    n => n
  | m+1,  n => (add m n) + 1

infixl:65 " + " => add
```

Thus, we can use them to get new numbers easily:

```lean
def one : Nat := 1
def ten : Nat := 10
def eleven : Nat := ten + one
def twelve : Nat := eleven + one
def thirteen : Nat := twelve + one
```

### Length of a List

The length of a list consists of traversing through the list and adding one for each element:

```lean
def length {α : Type} : List α → Nat
  | []      => 0
  | _ :: xs => 1 + length xs
```

The `length` function takes a list of any type `α` and returns a natural number (`Nat`). It uses pattern matching to handle two cases:

1. If the list is empty (`[]`), the length is `0`.
2. If the list has at least one element (`_ :: xs`), the length is 1 plus the length of the rest of the list (`xs`).

This function recursively processes the list, accumulating the total count of elements until it reaches the empty list.

# Dependent Function Types or Π-types

Dependent function types (also called Π-types) are function types where the result type depends on the argument value. These types generalize regular function types to allow more expressive types.

In Lean, dependent function types are written using the `Pi` keyword or the `∀` symbol. For example:

```lean
-- Binary dependent function type
def binaryDepFun (α : Type) (β : α → Type) : Type :=
  (a : α) → β a

-- Ternary dependent function type
def ternaryDepFun (α : Type) (β : α → Type) (γ : (a : α) → β a → Type) : Type :=
  (a : α) → (b : β a) → γ a b
```

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
