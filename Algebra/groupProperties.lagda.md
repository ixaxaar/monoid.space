<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Properties and APIs of groups](#properties-and-apis-of-groups)
  - [Homomorphisms](#homomorphisms)
    - [Magma homomorphism](#magma-homomorphism)
    - [Semigroupoid homomorphism](#semigroupoid-homomorphism)
    - [Small category homomorphism](#small-category-homomorphism)
    - [Semigroup homomorphism](#semigroup-homomorphism)
    - [Groupoid homomorphism](#groupoid-homomorphism)
  - [Subgroups](#subgroups)
  - [Cosets](#cosets)
  - [Quotient groups](#quotient-groups)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Properties and APIs of groups

```agda
module Algebra.groupProperties where

open import Level using (suc; _⊔_)
open import Types.equality using (Rel; _Preserves_⟶_)

open import Algebra.groups
open import Algebra.structures
```

## Homomorphisms

A function `f` is a homomorphism if given input `x ∈ X`, where X is a group-like structure, its output `y ∈ Y` where Y is also a group-like structure, such that `f` preserves the group-like structure of `X` in `Y`, i.e. it ensures that all relations what were valid in `X` remain valid in `Y`.

Let us first define a morphism:

```agda
module AbstractHomomorphism {f t ℓ} (From : Set f) (To : Set t) (_==_ : Rel To ℓ) where
  Morphism : Set _
  Morphism = From → To
```

The basic rules for any morphism to be a homomorphism are if it:

1. Preserves identity

```agda
  H-identity : Morphism → From → To → Set _
  H-identity ⟨_⟩ from to = ⟨ from ⟩ == to
```

2. Composes with operations

```agda
  H-unary-compose : Morphism → ♠ From → ♠ To → Set _
  H-unary-compose ⟨_⟩ ∙_ ∘_ = ∀ x → ⟨ ∙ x ⟩ == ( ∘ ⟨ x ⟩ )

  H-binary-compose : Morphism → ★ From → ★ To → Set _
  H-binary-compose ⟨_⟩ _∙_ _∘_ = ∀ x y → ⟨ x ∙ y ⟩ == ( ⟨ x ⟩ ∘ ⟨ y ⟩ )
```

Now, we define homomorphisms for various group-like structures we have discussed earlier.

### Magma homomorphism

```agda
module _ {f t ℓ₁ ℓ₂} (From : Magma f ℓ₁) (To : Magma t ℓ₂) where
  private
    module F = Magma From
    module T = Magma To

  open AbstractHomomorphism F.Data T.Data T._==_

  record IsMagmaHomomorphism ( ⟨_⟩ : Morphism) : Set (f ⊔ t ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      preserves-congruence    : ⟨_⟩ Preserves F._==_ ⟶ T._==_
      is-abstract-homomorphic : H-binary-compose ⟨_⟩ F._∙_ T._∙_
```

### Semigroupoid homomorphism

```agda
module _ {f t ℓ₁ ℓ₂} (From : Semigroupoid f ℓ₁) (To : Semigroupoid t ℓ₂) where
  private
    module F = Semigroupoid From
    module T = Semigroupoid To

  open AbstractHomomorphism F.Data T.Data T._==_

  record IsSemigroupoidHomomorphism ( ⟨_⟩ : Morphism) : Set (f ⊔ t ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      is-abstract-homomorphic : H-binary-compose ⟨_⟩ F._∙_ T._∙_
```

### Small category homomorphism

```agda
module _ {f t ℓ₁ ℓ₂} (From : SmallCategory f ℓ₁) (To : SmallCategory t ℓ₂) where
  private
    module F = SmallCategory From
    module T = SmallCategory To

  open AbstractHomomorphism F.Data T.Data T._==_

  record IsSmallCategoryHomomorphism ( ⟨_⟩ : Morphism) : Set (f ⊔ t ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      is-semigroupoid-homomorphic    : IsSemigroupoidHomomorphism F.semigroupoid T.semigroupoid ⟨_⟩
      preserves-identity             : H-identity ⟨_⟩ F.ε T.ε

    open IsSemigroupoidHomomorphism is-semigroupoid-homomorphic public
```

### Semigroup homomorphism

```agda
module _ {f t ℓ₁ ℓ₂} (From : Semigroup f ℓ₁) (To : Semigroup t ℓ₂) where
  private
    module F = Semigroup From
    module T = Semigroup To

  open AbstractHomomorphism F.Data T.Data T._==_

  record IsSemigroupHomomorphism ( ⟨_⟩ : Morphism ) : Set (f ⊔ t ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      is-magma-homomorphism  : IsMagmaHomomorphism F.magma T.magma ⟨_⟩

    open IsMagmaHomomorphism is-magma-homomorphism public
```

### Groupoid homomorphism

```aghabd
module _ {f t ℓ₁ ℓ₂} (From : Groupoid f ℓ₁) (To : Groupoid t ℓ₂) where
  private
    module F = Groupoid From
    module T = Groupoid To

  open AbstractHomomorphism F.Data T.Data T._==_

  record IsGroupoidHomomorphism ( ⟨_⟩ : Morphism ) : Set (f ⊔ t ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      is-smallcategory-homomorphic    : IsSmallCategoryHomomorphism F.smallcategory T.smallcategory ⟨_⟩
      preserves-inverse               : need equational reasoning

    open IsSmallCategoryHomomorphism is-smallcategory-homomorphic public
```

## Subgroups



## Cosets



## Quotient groups



