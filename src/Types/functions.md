****
[Contents](contents.html)
[Previous](Types.product.html)
[Next](Types.identity.html)

# Function Types

****

- [Function Types](#function-types)
    - [Introduction](#introduction)
    - [Function Types](#function-types-1)
        - [Definition and Notation](#definition-and-notation)
        - [Examples](#examples)
            - [Defining Functions](#defining-functions)
            - [Function Application](#function-application)
            - [Lambda Expressions](#lambda-expressions)
    - [Introduction to Dependent Types](#introduction-to-dependent-types)
        - [Motivating Example: Vectors](#motivating-example-vectors)
        - [Type Families](#type-families)
    - [Pi Types (Dependent Function Types)](#pi-types-dependent-function-types)
        - [Definition and Notation](#definition-and-notation-1)
        - [Examples in Lean](#examples-in-lean)
            - [Defining Pi Types](#defining-pi-types)
            - [Dependent Function Application](#dependent-function-application)
        - [Relationship to Simple Function Types](#relationship-to-simple-function-types)
    - [Currying and Uncurrying (Revisited)](#currying-and-uncurrying-revisited)
    - [Function Composition](#function-composition)
    - [Extensionality](#extensionality)

```lean
import Mathlib.Data.Vector
import Mathlib.Data.Fin.Basic
```

## Introduction

Recall that in type theory, every term has a type.  We've seen basic types like `Nat`, `Bool`, and `String`, and ways to combine types using products and co-products.  In this chapter, we'll explore *function types*, which represent functions between types, and the powerful generalization of function types known as Pi (Π) types (or dependent function types).

## Function Types

A function type, written `A → B`, represents functions that take an argument of type `A` and return a value of type `B`.  This is often read as "A to B".  The type `A` is the domain, and the type `B` is the codomain.

Mathematically, a function `f : A → B` is a relation between sets `A` and `B` such that for every `a ∈ A`, there is exactly one `b ∈ B` such that `(a, b)` is in the relation.  In type theory, functions are *first-class*: they can be arguments to other functions, returned as results, and stored in data structures.

### Examples

#### Lambda Expressions

We can also define functions anonymously, without giving them a name, using *lambda expressions*.  A lambda expression starts with the keyword `fun` (or the symbol `λ`), followed by the argument list, and then `=>` and the function body.

```lean
#check fun (n : Nat) => n * 2  -- fun n => n * 2 : ℕ → ℕ

def double : Nat → Nat := fun n => n * 2

#eval double 7 -- 14
```

Lambda expressions are particularly useful when passing functions as arguments to other functions.

## Dependent Function Types

A type family is a family of types indexed by a value of another type. Given a type `A`, a type family `B` indexed by `A` assigns a type `B a` to each value `a : A`.  Dependent types allow the type of a term to depend on the value of another term.

A dependent function type or Π-type, written `(a : A) → B a` (or `∀ (a : A), B a`), represents functions where the type of the return value depends on the value of the input. `B` is a type family indexed by `A`.

This can be read as "for all `a` of type `A`, a return type of `B a`".  This is a generalization of the simple function type `A → B`.  If `B` doesn't actually depend on `a`, then `(a : A) → B a` is the same as `A → B`.

### Examples

#### Defining Pi Types

```lean
-- A function that takes a length 'n' and returns a vector of zeros of that length.
def zeros (n : Nat) : Vector Nat n := Vector.replicate n 0

#check zeros  -- zeros : (n : ℕ) → Vector ℕ n
```

The type of `zeros` is a Pi type.  The return type, `Vector Nat n`, depends on the input value, `n`.

Another example: a function that gets the element at a specific index in a vector.  The index must be less than the length of the vector. Lean's `Fin n` type represents natural numbers less than `n`:

```lean
-- Get the element at index 'i' in a vector of length 'n'.
def Vector.get (v : Vector α n) (i : Fin n) : α := v.1[i]

#check Vector.get -- {α : Type} → {n : ℕ} → Vector α n → Fin n → α

```

The type of `Vector.get` is also a Pi Type. Note the use of the curly brackets `{}` to indicate implicit parameters.

Dependent function application looks just like regular function application:

```lean
#eval zeros 3    -- ⟨[0, 0, 0], by simp⟩
#eval (zeros 5).get ⟨2, by simp⟩  -- 0   (Accessing the element at index 2)
```

### Relationship to Simple Function Types

A simple function type `A → B` is just a special case of a Pi type where the return type *doesn't* depend on the input value. So, Lean can infer the use of non-dependent functions even while using dependent types.

```lean
def const_fun {A B : Type} (b : B) : (a : A) → B :=
  fun _ => b

#check @const_fun -- {A B : Type} → B → A → B
```

## Currying and Uncurrying (Revisited)

We saw Currying and Uncurrying already. This is a good time to revisit the concept and illustrate it with more involved examples, potentially also introducing the `curry` and `uncurry` functions from `Mathlib`.

## Function Composition
Define function composition mathematically and in Lean.

```lean
def compose {α β γ : Type} (g : β → γ) (f : α → β) : α → γ :=
  fun x => g (f x)

#check @compose
```

## Parametric Polymorphism

Parametric polymorphism allows us to write functions (and define types) that operate uniformly over different types. Instead of writing separate functions for `Nat → Nat`, `Bool → Bool`, and `String → String`, we can write a *single*, *generic* function that works for *any* type.

In Lean, parametric polymorphism is achieved using type parameters, indicated by curly braces `{}` or explicit type arguments. Let's look at an identity function, a function that return the input parameter it receives:

```lean
def identity {α : Type} (x : α) : α := x

#check identity  -- {α : Type} → α → α
#eval identity 5    -- 5
#eval identity "hello"  -- "hello"
#eval identity true     -- true
```

Here, `{α : Type}` introduces a *type parameter* `α`. The function `identity` can then be used with arguments of *any* type. Lean automatically infers the type parameter in many cases, which is why we don't need to write `identity Nat 5`.

Another example: a function that swaps the elements of a pair:

```lean
def swap {α β : Type} (pair : α × β) : β × α :=
  (pair.snd, pair.fst)

#check swap  -- {α β : Type} → α × β → β × α
#eval swap (1, "one")  -- ("one", 1)
```

`swap` works for pairs of *any* two types (which can even be different).


## Higher-Order Functions

Higher-order functions are functions that take other functions as arguments or return them as results. This is a powerful concept that enables code reuse and abstraction.  We've already seen some higher-order functions implicitly (like `compose`), but let's make it explicit.

### Functions as Arguments

Example:  A function that applies another function twice.

```lean
def applyTwice {α : Type} (f : α → α) (x : α) : α :=
  f (f x)

#check applyTwice  -- {α : Type} → (α → α) → α → α

def square (n : Nat) := n * n
#eval applyTwice square 3  -- 81 ( (3 * 3) * (3 * 3) )
```

`applyTwice` takes a function `f : α → α` as an argument and applies it twice to the input `x`.

### Functions as Results

Example: A function that takes a value and returns a function that always returns that value (a constant function).

```lean
def constantFunction {α β : Type} (b : β) : α → β :=
  fun _ => b

#check constantFunction -- {α β : Type} → β → α → β

def alwaysFive : Nat → Nat := constantFunction 5
#eval alwaysFive 10     -- 5
#eval alwaysFive 100    -- 5
```

`constantFunction` returns a *function*.

### Lifting

"Lifting" is a general term for taking a function that operates on one type and transforming it into a function that operates on a "wrapped" or "structured" version of that type. This is closely related to concepts like Functors and Applicatives, which we'll explore later.

Let use the `Option` type as an example.  `Option α` represents a value of type `α` that might be present (`some a`) or absent (`none`). We can "lift" a function `f : α → β` to a function `Option α → Option β`:

```lean
def optionMap {α β : Type} (f : α → β) : Option α → Option β
  | some a => some (f a)
  | none   => none

#check optionMap  -- {α β : Type} → (α → β) → Option α → Option β

def add1Opt : Option Nat → Option Nat := optionMap (fun n => n+1)
#eval add1Opt (some 5)  -- some 6
#eval add1Opt none       -- none
```

`optionMap` takes a function `f` and applies it to the value *inside* the `Option` (if it exists). This is a higher order function. There also happens to be a `lift` function.

## Extensionality

<<<Introduce the *axiom of extensionality*.  Explain that two functions are equal if they return equal results for all inputs. This is *not* provable in Lean's core type theory, but it's a commonly assumed axiom.>>>

```lean
-- This is an axiom, not a theorem!
axiom funext {α β : Type*} {f g : α → β} (h : ∀ x, f x = g x) : f = g
```

****
[Identity Types](./Types.identity.html)
