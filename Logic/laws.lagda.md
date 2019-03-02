<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Laws of Boolean Algebra](#laws-of-boolean-algebra)
  - [Monotone Laws](#monotone-laws)
    - [Operations](#operations)
    - [Associativity, Commutativity, Distributivity and Identity](#associativity-commutativity-distributivity-and-identity)
      - [Associativity](#associativity)
      - [Commutativity](#commutativity)
      - [Distributivity](#distributivity)
      - [Identity](#identity)
      - [Annihilator](#annihilator)
      - [Idempotence](#idempotence)
      - [Absorption](#absorption)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Laws of Boolean Algebra

We describe here some fundamental laws of boolean algebra, called "monotone laws". We then tackle some laws specific to Boolean algebra.

```agda
module Logic.laws where

open import Logic.logicBasics using (¬; not; xor; ⟂; ⊤; singleton)

open import Logic.equality using (Equiv; _≡_)

open import Types.relations using (Rel; Reflexive; Symmetric; Transitive; Congruent; Substitutive; Equivalence)

open import Lang.dataStructures using (Bool; true; false)

open import Types.typeBasics using (_×_; _,_)
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

### Associativity, Commutativity, Distributivity and Identity

For an operation `★`,

#### Associativity

$$
x \bigstar (y \bigstar z) \equiv (x \bigstar y) \bigstar z
$$

#### Commutativity

$$
x \bigstar y \equiv y \bigstar x
$$

#### Distributivity

$$
(x \bigstar y) \bigstar z \equiv x \bigstar y \x y \bigstar z
$$

#### Identity

$$
x \bigstar id_{bigstar} \equiv x
$$

These form the major laws of boolean algebra. There exists a bunch of others that we'll also see here. Note that for non-commutative systems of algebra, identity can exist in two forms: right and left, similarly for directional operations like distributivity, inverses, etc.

#### Annihilator

$$
x \bigstar id \equiv x
$$

#### Idempotence

Idempotence is a more specific law of boolean algebra:

$$
x \and x \equiv x
$$

#### Absorption

Another pair of reductive laws that apply only in boolean algebra:

$$
x \and (x \or y) \equiv x
x \or (x \and y) \equiv x
$$

For proving these laws we need an instance of the equivalence relation `==`:

```agda
module Laws {A : Set} (eq : Equivalence A) where
  module Eq₁ = Equivalence eq
  open Eq₁

  associativity : ★ A → Set
  associativity _★_ = (x y z : A)
          → (x ★ (y ★ z))
          == ((x ★ y) ★ z)

  commutativity : ★ A → Set
  commutativity _★_ = (x y : A)
          → (x ★ y)
          == (y ★ x)

  -- distributivity

  _distributesOverˡ_ : ★ A → ★ A → Set _
  _*_ distributesOverˡ _+_ =
    ∀ x y z → (x * (y + z)) == ((x * y) + (x * z))

  _distributesOverʳ_ : ★ A → ★ A → Set _
  _*_ distributesOverʳ _+_ =
    ∀ x y z → ((y + z) * x) == ((y * x) + (z * x))

  _distributesOver_ : ★ A → ★ A → Set _
  * distributesOver + = (* distributesOverˡ +) × (* distributesOverʳ +)

  -- identities

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

  -- interaction with zero

  leftZero : A → ★ A → Set _
  leftZero z _★_ = ∀ x → (z ★ x) == z

  rightZero : A → ★ A → Set _
  rightZero z _★_ = ∀ x → (x ★ z) == z

  zero : A → ★ A → Set _
  zero z ★ = leftZero z ★ × rightZero z ★

  -- inverses

  leftInverse : A → ∘ A → ★ A → Set _
  leftInverse e _⁻¹ _★_ = ∀ x → ((x ⁻¹) ★ x) == e

  rightInverse : A → ∘ A → ★ A → Set _
  rightInverse e _⁻¹ _★_ = ∀ x → (x ★ (x ⁻¹)) == e

  inverse : A → ∘ A → ★ A → Set _
  inverse e ⁻¹ ★ = (leftInverse e ⁻¹ ★) × (rightInverse e ⁻¹ ★)

  -- absorption

  _absorbs_ : ★ A → ★ A → Set _
  _∙_ absorbs _◌_ = ∀ x y → (x ∙ (x ◌ y)) == x

  absorptive : ★ A → ★ A → Set _
  absorptive ∙ ◌ = (∙ absorbs ◌) × (◌ absorbs ∙)

  -- idempotence

  _idempotentOn_ : ★ A → A → Set _
  _★_ idempotentOn x = (x ★ x) == x

  idempotent : ★ A → Set _
  idempotent ★ = ∀ x → ★ idempotentOn x
```


****
[Back to Contents](./contents.html)
