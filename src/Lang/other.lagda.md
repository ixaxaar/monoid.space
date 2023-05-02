****
[Contents](contents.html)
[Previous](Lang.functions.html)
[Next](Lang.syntaxQuirks.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Other Language Constructs](#other-language-constructs)
  - [Modules](#modules)
  - [Records](#records)
  - [Postulates](#postulates)
- [Others](#others)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Other Language Constructs

```agda
module Lang.other where

open import Lang.dataStructures renaming (_+_ to _⨦_)

open import Lang.functions using (_+_)
```

## Modules

Modules in Agda are used to organize code and manage namespaces, similar to packages in languages like Java or Python. They act as closures, with the indentation level indicating the scope of the module. Each Agda source file may contain one top-level module. Modules can be imported, as demonstrated in the import statements above.

Modules support nesting:

```agda
module nested where
  module X where
    x₁ = one

  module Y where
    x₂ = two

  sum = X.x₁ + Y.x₂
```

Importing modules:

```agda
open nested.X
x₁₁ = x₁ + one

open nested.Y renaming (x₂ to x₃)
x₂ = x₃ + one
```

Modules can also have parameters that are valid within their scope:

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
p23 = record { fst = two; snd = three }
```

You can use the `constructor` keyword to define records:

```agda
record Pair' (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

p45 : Pair' ℕ ℕ
p45 = four , five
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

list₂ : List' Bool
list₂ = L three vec3
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

# Others

In this section, we will discuss some of the quirks of Agda's syntax that might be helpful to know when writing code.

1. The backslash (`\`) and lambda (`λ`) characters can be used interchangeably to define anonymous functions:

```agda
example₁ = \ (A : Set)(x : A) → x
example₂ = λ A x → x
```

2. Implicit arguments can be specified using curly braces (`{}`). The compiler will try to infer the values of these arguments based on the context:

```agda
_++_ : {A : Set} → List A → List A → List A
```

3. Dot patterns (`.t`) can be used to indicate that the value of an argument can be uniquely determined by the patterns provided for other arguments:

```agda
root : (n : ℕ) → Square n → ℕ
root .(m × m) (sq m) = m
```

4. The `forall` keyword can be used to define dependent function types:

```agda
prop₃ : (forall (x : A) → C)  is-the-same-as   ((x : A) → C)
prop₄ : (forall x → C)        is-the-same-as   ((x : _) → C)
prop₅ : (forall x y → C)      is-the-same-as   (forall x → forall y → C)
```

5. Parentheses can be omitted when applying a function to multiple arguments:

```agda
(f a b) is-the-same-as ((f a) b)
```

These syntax quirks can be useful in making your Agda code more concise and expressive. As you become more familiar with the language, you may find yourself using these features more frequently.

****
[Quirks of Syntax](./Lang.syntaxQuirks.html)
