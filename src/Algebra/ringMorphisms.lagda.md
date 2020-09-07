****
[Contents](contents.html)
[Previous](Algebra.rings2.html)
[Next](Algebra.fields.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Ring Morphisms](#ring-morphisms)
  - [Ring Homomorphism](#ring-homomorphism)
  - [Ring Automorphism](#ring-automorphism)
  - [Ring Monomorphism](#ring-monomorphism)
  - [Ring Isomorphism](#ring-isomorphism)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Ring Morphisms

```agda
module Algebra.ringMorphisms where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Types.relations
open import Types.equality
open import Types.functions2

open import Algebra.groups
open import Algebra.groups2
open import Algebra.groupMorphisms

open import Algebra.rings
open import Algebra.rings2
```

Ring morphisms are maps between two rings that preserve the ring structure. These follow the same theme that the group-like objects did in [Group Morphisms](./Algebra.morphisms.html).

## Ring Homomorphism

```agda
module _ {f t ℓ₁ ℓ₂} (From : Ring f ℓ₁) (To : Ring t ℓ₂) where
  private
    module F = Ring From
    module T = Ring To

  open Homomorphism F.Data T.Data T._≈_

  record IsRingHomomorphism (𝕄⟦_⟧ : Morphism) : Set (f ⊔ t ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      +-isGroupHomomorphism     : IsGroupHomomorphism F.+-group T.+-group 𝕄⟦_⟧
      *-isMonoidHomomorphism    : IsMonoidHomomorphism F.*-monoid T.*-monoid 𝕄⟦_⟧
```

## Ring Automorphism

Automorphisms are pretty straightforward:

```agda
module _ {f t ℓ} (Self : Ring f ℓ) where
  private
    module F = Ring Self
    module T = Ring Self

  open Homomorphism F.Data T.Data T._≈_

  record IsRingAutomorphism (𝕄⟦_⟧ : Morphism) : Set (f ⊔ t ⊔ ℓ) where
    field
      +-isGroupHomomorphism     : IsGroupHomomorphism F.+-group T.+-group 𝕄⟦_⟧
      *-isMonoidHomomorphism    : IsMonoidHomomorphism F.*-monoid T.*-monoid 𝕄⟦_⟧
```

## Ring Monomorphism

For monomorphism we add the injective condition:

```agda
module _ {f t ℓ₁ ℓ₂} (From : Ring f ℓ₁) (To : Ring t ℓ₂) where
  private
    module F = Ring From
    module T = Ring To

  open Homomorphism F.Data T.Data T._≈_

  record IsRingMonomorphism (𝕄⟦_⟧ : Morphism) : Set (f ⊔ t ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      is-ring-homomorphism : IsRingHomomorphism From To 𝕄⟦_⟧
      is-injective : Injective 𝕄⟦_⟧
```

## Ring Isomorphism

****
[Fields and family](./Algebra.fields.html)
