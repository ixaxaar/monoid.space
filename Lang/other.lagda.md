****
[Contents](contents.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Other language constructs](#other-language-constructs)
  - [Modules](#modules)
  - [Records](#records)
  - [Postulates](#postulates)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Other language constructs

```agda
module Lang.other where

open import Lang.dataStructures

open import Lang.functions using (_+_)
```

## Modules

Modules are essentially a "bunch" of definitions. They behave as closures with the indentation the indicator of the extent, similar to python. A Module object `object` can be accessed with `ModuleName.object`.

```agda
module nested where
  module X where
    x₁ = one

  module Y where
    x₂ = two

  sum = X.x₁ + Y.x₂
```

Modules can be "opened" or imported, like so:

```agda
open nested.X
x₁₁ = x₁ + one

open nested.Y renaming (x₂ to x₃)
x₂ = x₃ + one
```

Modules can have parameters and be used to defined closures:

```agda
module Sort (A : Set)(_≤_ : A → A → Bool) where
  insert : A → List A → List A
  insert x [] = x :: []
  insert x (y :: ys) with x ≤ y
  insert x (y :: ys)    | true  = x :: y :: ys
  insert x (y :: ys)    | false = y :: insert x ys

  sort : List A → List A
  sort []       = []
  sort (x :: xs) = insert x (sort xs)
```

Thus, modules primarily help in structuring code. Modules also provide additional functionalities like private and public components, we tackle them as and when we need to.

## Records

Tuples are called as `Record`s in Agda. Some examples are:

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

An object of `Pair` can be constructed as:

```agda
p23 : Pair ℕ ℕ
p23 = record { fst = two; snd = three }
```

The `constructor` keyword can be specified to construct the pairs:

```agda
record Pair' (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

p45 : Pair' ℕ ℕ
p45 = four , five
```

The values of a record can be pattern matched upon:

```agda
left : Pair' ℕ ℕ → ℕ
left (x , y) = x
```

A record can be parameterized:

```agda

record List' (A : Set) : Set where
  constructor L
  field
    length : ℕ
    vector : Vec A length

list₂ : List' Bool
list₂ = L three vec3
```

All `Data` definitions have an equivalent `Record` definiton, however `Record`s are preferred whenever possible as a convention. Records have the obvious advantage of providing `getters` and `setters` for free.

## Postulates

`postulate`s are another Agda language construct. These facilitate defining some type without the actual implementation.

```agda
postulate
  A B    : Set
  a      : A
  b      : B
  _=AB=_ : A → B → Set
  a==b   : a =AB= b
```

or

```agda
data False : Set where

postulate bottom : False
```

****
[Debugging](./Lang.debugging.html)
