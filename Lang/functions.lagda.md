****
[Contents](contents.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Functions](#functions)
  - [Pattern matching functions](#pattern-matching-functions)
    - [The Logical Not](#the-logical-not)
    - [The logical AND](#the-logical-and)
    - [The logical OR](#the-logical-or)
  - [Recursive functions](#recursive-functions)
    - [Addition of natural numbers](#addition-of-natural-numbers)
- [List functions](#list-functions)
  - [List concatenation](#list-concatenation)
  - [Length](#length)
  - [Map](#map)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Functions

Functions, also being technically types, can sometimes have practically simpler syntax than data while serving the same purpose.

```agda
module Lang.functions where

open import Lang.dataStructures
```

## Pattern matching functions

### The Logical Not

The simplest of functions simply match patterns. For example the function for `not`:

```agda
not : Bool → Bool
not true = false -- return false if we are given a true
not false = true -- return a true if we are given a false
```

we could also use wildcard type like this:

```agda
not₁ : Bool → Bool
not₁ true = false -- return false if we are given a true
not₁ _ = true -- return true in all other cases
```

### The logical AND

```agda
_∧_ : Bool → Bool → Bool
true ∧ whatever = whatever -- true AND whatever is whatever
false ∧ whatever = false -- false AND whatever is false

infixr 6 _∧_
```

### The logical OR

```agda
_∨_ : Bool → Bool → Bool
true ∨ whatever = true -- true or whatever is true
false ∨ whatever = whatever -- false or whatever is whatever

infixr 6 _∨_
```

These functions can be applied as:

```agda
notTrue : Bool
notTrue = not true

false₁ : Bool
false₁ = true ∧ false

true₁ : Bool
true₁ = true ∨ false ∨ false₁
```

## Recursive functions

### Addition of natural numbers

Here we follow a similar pattern as in `data`, we define:

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

This function takes a type as a parameter `A`, and hence can work on `List`s of any type `A`. This feature of functions is called "parametric polymorphism". These functions tend to work on higher levels of abstraction, and work for all list types.

Note that the curly braces `{}` are called "implicit arguments" in Agda. Values of implicit arguments are derived from other arguments' values and types by solving type equations. You don’t have to apply them or pattern match on them explicitly (though they can be explicitly stated like `{A = A}`). Practically, they help in defining the scope of types.

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

![map](./map.png)

```agda
map : {A B : Set} → List A → (A → B) → List B
map [] f = []
map (x :: xs) f = (f x) :: (map xs f)
```

Here, we apply the function `addOne` to a list, using `map`:

```agda
addOne : ℕ → ℕ
addOne x  = x + one

oneAdded : List ℕ
oneAdded = map (one :: two :: three :: four :: []) addOne
```


****
[Proofs as Data](./Lang.proofsAsData.html)
