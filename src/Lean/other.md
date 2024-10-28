****
[Contents](contents.html)
[Previous](Lean.functions.html)
[Next](Lean.debugging.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Additional Language Features and Syntax](#additional-language-features-and-syntax)
  - [Modules](#modules)
  - [Records](#records)
  - [Postulates](#postulates)
  - [Syntactic Sugar and Alternative Syntax](#syntactic-sugar-and-alternative-syntax)
    - [Common Parameters](#common-parameters)
    - [Different Ways of Defining `data`](#different-ways-of-defining-data)
    - [Implicit Arguments](#implicit-arguments)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Additional Language Features and Syntax

```agda
module Lean.other where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
```

## Modules

Modules in Agda are used to organize code and manage namespaces, similar to packages in languages like Java or Python. They act as closures, with the indentation level indicating the scope of the module. Each Agda source file may contain one top-level module. Modules can be imported, as demonstrated in the import statements above.

Modules support nesting:

```agda
module nested where
  module X where
    x₁ = 1

  module Y where
    x₂ = 2

  sum = X.x₁ + Y.x₂
```

Importing modules:

```agda
open nested.X
x₁₁ = x₁ + 1

open nested.Y renaming (x₂ to x₃)
x₂ = x₃ + 1
```

Modules can also have parameters that are valid within their scope:

```agda
module Sort (A : Set)(_≤_ : A → A → Bool) where
  insert : A → List A → List A
  insert x [] = x ∷ []
  insert x (y ∷ ys) with x ≤ y
  insert x (y ∷ ys)    | true  = x ∷ y ∷ ys
  insert x (y ∷ ys)    | false = y ∷ insert x ys

  sort : List A → List A
  sort []       = []
  sort (x ∷ xs) = insert x (sort xs)
```

## Records

In Agda, tuples are called `Record`s. Here are some examples:

A tuple of `Bool` and `ℕ`:

```agda
record R : Set where
  field
    r₁ : Bool
    r₂ : ℕ
```

A generic tuple:

```agda
record Pair (A B : Set) : Set where
  field
    fst : A
    snd : B
```

An instance of `Pair` can be constructed as:

```agda
p23 : Pair ℕ ℕ
p23 = record { fst = 2; snd = 3 }
```

You can use the `constructor` keyword to define records:

```agda
record Pair' (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

p43 : Pair' ℕ ℕ
p43 = 4 , 3
```

The values of a record can be pattern matched:

```agda
left : Pair' ℕ ℕ → ℕ
left (x , y) = x
```

A record can also be parameterized:

```agda
record List' (A : Set) : Set where
  constructor L
  field
    length : ℕ
    vector : Vec A length

exampleVec : Vec Bool 3
exampleVec = true ∷ false ∷ true ∷ []

list₂ : List' Bool
list₂ = L 3 exampleVec
```

All `Data` definitions have equivalent `Record` definitions, but using `Record`s is preferred as a convention. Records have the advantage of automatically providing getters and setters.

## Postulates

`postulate`s are another language construct in Agda. They allow you to define a type without providing an actual implementation.

```agda
postulate
  A B    : Set
  a      : A
  b      : B
  _=AB=_ : A → B → Set
  a==b   : a =AB= b
```

```agda
data False : Set where

postulate bottom : False
```

## Syntactic Sugar and Alternative Syntax

These are shorthand forms of commonly used constructs and alternative ways to express code that you might find helpful or convenient.

### Common Parameters

Implicit parameters, such as `{m : ℕ}`, that are common to all constructors can be abstracted out into the data definition:

```agda
data _≤′_ : ℕ → ℕ → Set where
  ≤′-refl : {m : ℕ} →                       m ≤′ m
  ≤′-step : {m : ℕ} → {n : ℕ} →  m ≤′ n  →  m ≤′ suc n
```

This is equivalent to:

```agda
data _≤′₁_ (m : ℕ) : ℕ → Set where
  ≤′₁-refl :                       m ≤′₁ m
  ≤′₁-step : {n : ℕ} →  m ≤′₁ n  →  m ≤′₁ suc n
```

### Different Ways of Defining `data`

The technique above can also be applied to concrete parameters:

```agda
data _≤″_ : ℕ → ℕ → Set where
  ≤″ : ∀ {m n k} → m + n ≡ k → m ≤″ k
```

This is equivalent to:

```agda
data _≤″₁_ (m : ℕ) : ℕ → Set where
  ≤+ : ∀ {n k} → m + n ≡ k → m ≤″₁ k
```

Which is also equivalent to:

```agda
data _≤″₂_ (m : ℕ) (k : ℕ) : Set where
  ≤+ : ∀ {n} → m + n ≡ k → m ≤″₂ k
```

### Implicit Arguments

Arguments that can be inferred by the compiler can be left out with an `_`:

```agda
length : (A : Set) (len : ℕ) → Vec A len → ℕ
length A zero [] = zero
length A len somevec = len
```

```agda
length' : (A : Set) (len : ℕ) → Vec A len → ℕ
length' A zero [] = zero
length' A len _   = len
```

```agda
length'' : (A : Set) (len : ℕ) → Vec A len → ℕ
length'' A zero [] = zero
length'' _ len _   = len
```

Using `_` for inferring arguments can be helpful in making your code more concise. However, be careful when using this feature, as it can also lead to confusion if used inappropriately.


****
[Debugging](./Lean.debugging.html)
