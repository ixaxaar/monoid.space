****
[Contents](contents.html)
[Previous](Algebra.groups2.html)
[Next](Algebra.rings.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Morphisms](#morphisms)
  - [Homomorphisms](#homomorphisms)
    - [Magma homomorphism](#magma-homomorphism)
    - [Semigroup homomorphism](#semigroup-homomorphism)
    - [Monoid Homomorphism](#monoid-homomorphism)
    - [Group Homomorphism](#group-homomorphism)
  - [Endomorphism](#endomorphism)
    - [Monoid endomorphism](#monoid-endomorphism)
    - [Group endomorphism](#group-endomorphism)
  - [Isomorphism](#isomorphism)
  - [Automorphism](#automorphism)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Morphisms

```agda
module Algebra.morphisms where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Types.relations
open import Types.equality

open import Algebra.groups
open import Algebra.groups2
```

A morphism is a more general concept that applies not only to groups but also to pretty much all algebraic objects. It can be defined as a structure-preserving map. In the context of group-like objects, a morphism between any two objects `X` and `Y` embeds `X` in `Y` while ensuring the structure of `X` is preserved.

Let us first define a morphism:

```agda
module Homomorphism {f t ℓ} (From : Set f) (To : Set t) (_==_ : Rel To ℓ) where
  Morphism : Set _
  Morphism = From → To
```

In the family of groups, these are the main kinds of morphisms:

1. Homomorphism
2. Endomorphism
3. Isomorphism
4. Automorphism

## Homomorphisms

A map (function) `𝔽` is a homomorphism if given input `x ∈ (X, •)`, where X is a group-like structure, its output `y ∈ (Y, ∘)` where Y is also a group-like structure, such that `𝔽` preserves the group-like structure of `X` in `Y`, i.e. it ensures that all relations what were valid in `X` remain valid in `Y`. More formally,

Given two groups, `(X, •)` and `(Y, ∘)`, `𝔽 : X → Y` is a homomorphism if:

$$
∀ x₁, x₂ ∈ X, 𝔽⟦ x₁ • x₂ ⟧ = 𝔽⟦ x₁ ⟧ ∘ 𝔽⟦ x₂ ⟧
$$

The basic rules for any morphism to be a homomorphism are if it:

1. Preserves identity

An identity homomorphism when applied to a structure produces the same structure.

```agda
  identity-preservation : Morphism → From → To → Set _
  identity-preservation 𝕄⟦_⟧ from to = 𝕄⟦ from ⟧ == to
```

2. Composes with operations

If `𝔽` is a homomorphism from `X → Y`, and `⋅` and `∘` are both unary or both binary operations operating on `X` and `Y` respectively, then `𝔽` composes with the two operations in the following ways:

```agda
  compose-unary : Morphism → ♠ From → ♠ To → Set _
  compose-unary 𝕄⟦_⟧ ∙_ ∘_ = ∀ x → 𝕄⟦ ∙ x ⟧ == ( ∘ 𝕄⟦ x ⟧ )

  compose-binary : Morphism → ★ From → ★ To → Set _
  compose-binary 𝕄⟦_⟧ _∙_ _∘_ = ∀ x y → 𝕄⟦ x ∙ y ⟧ == ( 𝕄⟦ x ⟧ ∘ 𝕄⟦ y ⟧ )
```


Now, we define homomorphisms for various group-like structures we have discussed earlier.

### Magma homomorphism

```agda
module _ {f t ℓ₁ ℓ₂} (From : Magma f ℓ₁) (To : Magma t ℓ₂) where
  private
    module F = Magma From
    module T = Magma To

  open Homomorphism F.Data T.Data T._==_

  record IsMagmaHomomorphism (𝕄⟦_⟧ : Morphism) : Set (f ⊔ t ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      preserves-congruence    : 𝕄⟦_⟧ Preserves F._==_ ⟶ T._==_
      preserves-composition   : compose-binary 𝕄⟦_⟧ F._∙_ T._∙_
```

### Semigroup homomorphism

```agda
module _ {f t ℓ₁ ℓ₂} (From : Semigroup f ℓ₁) (To : Semigroup t ℓ₂) where
  private
    module F = Semigroup From
    module T = Semigroup To

  open Homomorphism F.Data T.Data T._==_

  record IsSemigroupHomomorphism (𝕄⟦_⟧ : Morphism ) : Set (f ⊔ t ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      is-magma-homomorphism  : IsMagmaHomomorphism F.magma T.magma 𝕄⟦_⟧

    open IsMagmaHomomorphism is-magma-homomorphism public
```

### Monoid Homomorphism

```agda
module _ {f t ℓ₁ ℓ₂} (From : Monoid f ℓ₁) (To : Monoid t ℓ₂) where
  private
    module F = Monoid From
    module T = Monoid To

  open Homomorphism F.Data T.Data T._==_

  record IsMonoidHomomorphism (𝕄⟦_⟧ : Morphism ) : Set (f ⊔ t ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      is-semigroup-homomorphism  : IsSemigroupHomomorphism F.semigroup T.semigroup 𝕄⟦_⟧
      preserves-identity         : identity-preservation 𝕄⟦_⟧ F.ε T.ε

    open IsSemigroupHomomorphism is-semigroup-homomorphism public
```

### Group Homomorphism

```agda
module _ {f t ℓ₁ ℓ₂} (From : Group f ℓ₁) (To : Group t ℓ₂) where
  private
    module F = Group From
    module T = Group To

  open Homomorphism F.Data T.Data T._==_

  record IsGroupHomomorphism (𝕄⟦_⟧ : Morphism ) : Set (f ⊔ t ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      is-monoid-homomorphism  : IsMonoidHomomorphism F.monoid T.monoid 𝕄⟦_⟧
      preserves-inverse       : compose-unary 𝕄⟦_⟧ F._⁻¹ T._⁻¹

    open IsMonoidHomomorphism is-monoid-homomorphism public
```

## Endomorphism

An Endomorphism is a homomorphism where `From` and `To` are the same objects.

### Monoid endomorphism

```agda
module _ {f ℓ} (Self : Monoid f ℓ) where
  private
    module S = Monoid Self

  open Homomorphism S.Data S.Data S._==_

  record IsMonoidAutomorphism (𝕄⟦_⟧ : Morphism) : Set (f ⊔ ℓ) where
    field
      is-homomorphism : IsMonoidHomomorphism Self Self 𝕄⟦_⟧
```

### Group endomorphism

```agda
module _ {f ℓ} (Self : Group f ℓ) where
  private
    module S = Group Self

  open Homomorphism S.Data S.Data S._==_

  record IsGroupAutomorphism (𝕄⟦_⟧ : Morphism) : Set (f ⊔ ℓ) where
    field
      is-homomorphism : IsGroupHomomorphism Self Self 𝕄⟦_⟧
```

## Isomorphism

An group isomorphism is a homomorphism with an additional property - bijection (one-to-one + onto). Bijection implies an isomorphism is a homomorphism such that the inverse of the homomorphism is also a homomorphism. Practically, an isomorphism is an equivalence relation. Often in mathematics one encounters the phrase "equal upto isomorphism" meaning isomorphism serves as equality for all practical purposes.

![Injection vs Surjection vs Bijection](../artwork/functions.png)

## Automorphism

An automorphism is a endomorphism which is also an isomorphism.

****
[Rings and family](./Algebra.rings.html)
