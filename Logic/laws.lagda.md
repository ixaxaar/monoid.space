****
[Contents](contents.html)
[Previous](Logic.equality.html)
[Next](Logic.decidability.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Laws of Boolean Algebra](#laws-of-boolean-algebra)
  - [Monotone Laws](#monotone-laws)
    - [Operations](#operations)
    - [Laws](#laws)
      - [Associativity](#associativity)
      - [Commutativity](#commutativity)
      - [Distributivity](#distributivity)
      - [Identity](#identity)
      - [Annihilation](#annihilation)
      - [Idempotence](#idempotence)
      - [Absorption](#absorption)
  - [∧ and ∨](#%E2%88%A7-and-%E2%88%A8)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Laws of Boolean Algebra

We describe here some fundamental laws of boolean algebra, called "monotone laws". We then tackle some laws specific to Boolean algebra.

```agda
module Logic.laws where

open import Lang.dataStructures using (Bool; true; false)
open import Types.product using (_×_; _,_)
open import Types.relations using (Rel; Equivalence)
open import Logic.logicBasics using (¬; not; xor; ⟂; ⊤; singleton)
open import Logic.equality using (Equiv; _≡_)
```

## Monotone Laws

Monotone laws are ones in which the inputs and outputs change monotonically, or the output either remains unchanged on changing inputs or changes in the same way as the input.

### Operations

We first need to define operations in an abstract way before we proceed with laws on these operations. We used types to define families (types) of operations:

A unary operation can be defined as:

```agda
∘ : Set → Set
∘ A = A → A
```

A binary operation `★ A` can be defined as:

```agda
★_ : Set → Set
★ A = A → A → A
```

Here `*_` constructs a type family of operations that operate on given type `A`.

For proving these laws we need an instance of the equivalence relation `==`.

```agda
module BooleanLaws {A : Set} (eq : Equivalence A) where
  module Eq₁ = Equivalence eq
  open Eq₁
```

### Laws

For an operation `★`,

#### Associativity

$$
x ★ (y ★ z) ≡ (x ★ y) ★ z
$$

![Fig 1: Associative property](associative.png)

```agda
  associativity : ★ A → Set
  associativity _★_ = (x y z : A)
          → (x ★ (y ★ z))
          == ((x ★ y) ★ z)
```

#### Commutativity

$$
x ★ y ≡ y ★ x
$$

![Fig 2: Commutative property](commutative.png)

```agda
  commutativity : ★ A → Set
  commutativity _★_ = (x y : A)
          → (x ★ y)
          == (y ★ x)
```

#### Distributivity


$$
( x ★ y ) ★ z ≡ x ★ y × y ★ z
$$

![Fig 3: Distributive property](distributive.png)

```agda
  _distributesOverˡ_ : ★ A → ★ A → Set _
  _*_ distributesOverˡ _+_ =
    ∀ x y z → (x * (y + z)) == ((x * y) + (x * z))

  _distributesOverʳ_ : ★ A → ★ A → Set _
  _*_ distributesOverʳ _+_ =
    ∀ x y z → ((y + z) * x) == ((y * x) + (z * x))

  _distributesOver_ : ★ A → ★ A → Set _
  * distributesOver + = (* distributesOverˡ +) × (* distributesOverʳ +)
```

#### Identity

$$
x ★ id_{★} ≡ x
$$

![Fig 4: Identity](identity.png)

These form the major laws of boolean algebra. There exists a bunch of others that we'll also see here. Note that for non-commutative systems of algebra, identity can exist in two forms: right and left, similarly for directional operations like distributivity, inverses, etc.

```agda
  identityₗ : A → ★ A → Set
  identityₗ x _★_ =  (y : A)
          → (x ★ y)
          == x

  identityᵣ : A → ★ A → Set
  identityᵣ x _★_ = (y : A)
          → (y ★ x)
          == x

  identity : A → ★ A → Set
  identity x ★ = (identityₗ x ★) × (identityᵣ x ★)
```

#### Annihilation

$$
x ★ id ≡ x
$$

![Fig 5: Elimination](elimination.png)

```agda
  leftZero : A → ★ A → Set _
  leftZero z _★_ = ∀ x → (z ★ x) == z

  rightZero : A → ★ A → Set _
  rightZero z _★_ = ∀ x → (x ★ z) == z

  zero : A → ★ A → Set _
  zero z ★ = leftZero z ★ × rightZero z ★
```

#### Idempotence

Idempotence is a more specific law of boolean algebra:

$$
x ∧ x ≡ x
$$

![Fig 6: Idempotence](idempotence.png)

```agda
  _idempotentOn_ : ★ A → A → Set _
  _★_ idempotentOn x = (x ★ x) == x

  idempotent : ★ A → Set _
  idempotent ★ = ∀ x → ★ idempotentOn x
```

#### Absorption

Another pair of reductive laws that apply only in boolean algebra:

$$
x ∧ (x ∨ y) ≡ x
x ∨ (x ∧ y) ≡ x
$$

```agda
  _absorbs_ : ★ A → ★ A → Set _
  _∙_ absorbs _◌_ = ∀ x y → (x ∙ (x ◌ y)) == x

  absorptive : ★ A → ★ A → Set _
  absorptive ∙ ◌ = (∙ absorbs ◌) × (◌ absorbs ∙)
```

## ∧ and ∨

The logical `AND` and `OR` operators satisfy the above laws:

```agda
  open import Logic.logicBasics
  open import Types.operations _==_
```

  ∨-assoc : associativity _∨_
  ∨-assoc true  y z = refl
  ∨-assoc false y z = refl

  ∨-comm : Commutative _∨_
  ∨-comm true  true  = refl
  ∨-comm true  false = refl
  ∨-comm false true  = refl
  ∨-comm false false = refl

  ∨-identityˡ : LeftIdentity false _∨_
  ∨-identityˡ _ = refl

  ∨-identityʳ : RightIdentity false _∨_
  ∨-identityʳ false = refl
  ∨-identityʳ true  = refl

  ∨-identity : Identity false _∨_
  ∨-identity = ∨-identityˡ , ∨-identityʳ

  ∨-zeroˡ : LeftZero true _∨_
  ∨-zeroˡ _ = refl

  ∨-zeroʳ : RightZero true _∨_
  ∨-zeroʳ false = refl
  ∨-zeroʳ true  = refl

  ∨-zero : Zero true _∨_
  ∨-zero = ∨-zeroˡ , ∨-zeroʳ

  ∨-inverseˡ : LeftInverse true not _∨_
  ∨-inverseˡ false = refl
  ∨-inverseˡ true  = refl

  ∨-inverseʳ : RightInverse true not _∨_
  ∨-inverseʳ x = ∨-comm x (not x) ⟨ trans ⟩ ∨-inverseˡ x

  ∨-inverse : Inverse true not _∨_
  ∨-inverse = ∨-inverseˡ , ∨-inverseʳ

****
[Decidability](./Logic.decidability.html)
