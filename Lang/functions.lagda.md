<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Functions](#functions)
  - [Pattern matching functions](#pattern-matching-functions)
    - [The Logical Not](#the-logical-not)
    - [The logical AND](#the-logical-and)
    - [The logical OR](#the-logical-or)
  - [Recursive](#recursive)
    - [Addition of natural numbers](#addition-of-natural-numbers)
- [List functions](#list-functions)
  - [List concatenation](#list-concatenation)
  - [Length](#length)
  - [Map](#map)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Functions

Functions, also being technically types, can sometimes have practically simpler syntax.

```agda
module Lang.functions where

open import Lang.dataStructures using (
  Bool; true; false;
  ⊥; ⊤; ℕ; List;
  one; two; three; four; five; six; seven; eight; nine; ten; zero; succ;
  _::_; [])

open import Lang.proofsAsData using (_≡_)
```

## Pattern matching functions

### The Logical Not

The simplest of functions simply match patterns. For example the fuction for `not`:

```agda
not : Bool → Bool
not true = false
not false = true
```

### The logical AND

```agda
_∧_ : Bool → Bool → Bool
true ∧ x = x
false ∧ x = false

infixr 6 _∧_
```

### The logical OR

```agda
_∨_ : Bool → Bool → Bool
true ∨ x = true
false ∨ x = x

infixr 6 _∨_
```

These can be applied as:

```agda
notTrue : Bool
notTrue = not true

false₁ : Bool
false₁ = true ∧ false

true₁ : Bool
true₁ = true ∨ false ∨ false₁
```

## Recursive

### Addition of natural numbers

Here we follow a similar pattern as in data, we define:

- the identity condition, what happens on addition with zero in this case
- and how to successively build up the final value

```agda
_+_ : ℕ → ℕ → ℕ
zero + n = n
succ m + n = succ (m + n)

infixl 6 _+_
```
Thus, we can use them to get new numbers easily:

```agda
eleven = ten + one
twelve = eleven + one
thirteen = twelve + one
```

# List functions

## List concatenation

```agda
_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

infixr 5 _++_
```

This function takes a type as a parameter `A`, and hence can work on `List`s of any type `A`. This feature of functions is called "parametric polymorphism". These functions tend to work on higher levels of abstraction, with disregard to the types inside.

Note that the curly braces `{}` are called "implicit arguments" in Agda. Values of implicit arguments are derived from other arguments' values and types by solving type equations. You don’t have to apply them or pattern match on them explicitly. Practically, they help in defining the scope of types.

## Length

The length of a list consists of traversing through the list and adding one for each element:

```agda
length : List ⊤ → ℕ
length [] = zero
length (x :: xs) = one + (length xs)
```

## Map

We implement the `map` function, of "map-reduce" fame, for `List`s:
A map function for a `List` is a function that applies a lambda (un-named) function to all elements of a `List`.

If `f` were a lambda function, map-ing `f` over `List(a, b, c, d)` would produce `List(f(a), f(b), f(c), f(d))`

```agda
map : {A B : Set} → List A → (A → B) → List B
map [] f = []
map (x :: xs) f = (f x) :: (map xs f)
```

```agda
addOne : ℕ → ℕ
addOne x  = x + one

oneAdded : List ℕ
oneAdded = map (one :: two :: three :: four :: []) addOne
```
Here, we apply the function `addOne` to a list, using `map`.

****
[Back to Contents](./contents.html)
