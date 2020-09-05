****
[Contents](contents.html)
[Previous](HoTT.introduction.html)
[Next](HoTT.paths.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Homotopy Theory](#homotopy-theory)
  - [Overview](#overview)
  - [Paths](#paths)
  - [Homotopy](#homotopy)
  - [Fundamental group](#fundamental-group)
  - [∞-groupoid](#-groupoid)
    - [Groupoid](#groupoid)
    - [∞-groupoid](#-groupoid-1)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Homotopy Theory


```agda
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Types.product
open import Types.relations
open import Types.equality
open import Types.functions

module HoTT.homotopy {a ℓ} {A : Set a} (_==_ : Rel A ℓ) where
  open import Types.operations (_==_)
```

## Overview

The notion of "space" generally invokes thought of a geometrical structure. The usual spaces one might have encountered are Euclidean spaces which fit this intuition. In Algebraic Geometry (of which Homotopy Theory is a part), however, the notion of a space is abstract, and as a consequence while the well known spaces fit into the definition, so do many other kinds of objects.

1. A topological space is a set of points endowed with an additional structure called a "topology".
2. There is a condition called "continuity" imposed on this space, and hence also concepts like a "neighborhood" of points.
3. A path is a line joining two points in a topological space. These are also called as continuous maps.
4. There can be multiple paths between any two points some of which might be similar in some sense, hence there is a notion of an equivalence between paths, called "homotopy".

Homotopy Theory studies the characteristics of homotopies of paths.

## Paths

Technically, in a topological space 𝕏, a path between two points `x` and `y` ∈ 𝕏 can be represented as a function `f` that takes a continuous value `t` and returns a point on the path `f(t)` such that the first point is `x` $f(0) = x$ and the last point is `y` $f(1) = y$ and $0 ≤ t ≤ 1$. Paths thus represented are continuous functions.

![Figure 1: Path](/artwork/pathType.png)

## Homotopy

We could take any two paths between the same points and stretch / squeeze one path into another. This process can be used to capture relationships between two paths and is called _homotopy_. More formally,

A _homotopy_ between two paths `p(t)` and `q(t)` is defined as a continuous function `H(t, h)` such that:

- $H(t, 0) = p(t)$
- $H(t, 1) = q(t)$
- $H(0, h) = x$
- $H(1, h) = y$

There can exist multiple paths between two objects and hence multiple homotopies between them. Homotopies can be thought of as 2-dimensional paths or path-of-path if paths are 1-dimensional paths.

![Figure 2: Homotopy](/artwork/homotopy.png)

## Fundamental group

Two homotopies `H1` and `H2` can themselves be called equivalent if $H(0, h) = H(1, h) = x₀$, i.e. if `x` and `y` are the same point. We can use this equivalence relation and the fact that homotopies have inverses (with loops in the opposite direction), to build a group structure around these homotopies, called as the _fundamental group_.

Formally, for any point `x` in a topological space 𝕏, the fundamental group is the group over
- Homotopy equivalence classes as objects at point `x₀` denoted $π₁(𝕏, x₀)$.
- A product operation defined on these equivalence classes a such:

Given two paths / loops (γ₁ and γ₂), their product is:

```math
γ₁ ♢ γ₂ : [1,0] → 𝕏
γ₁ ♢ γ₂ = λ t → if (0 < t < 1÷2) γ₁ (2 * t) else  γ₂ (2 * t - 1)
```

Thus the loop `γ₁ ♢ γ₂` first follows the loop γ₁ with "twice the speed" and then follows γ₂ with "twice the speed". It is to be noted that we consider all equivalence classes of loops instead of considering all loops as loops belonging to one equivalence class can be treated as the same.

![Figure 3: Fundamental Group](/artwork/fundamental_group.png)

Note that we take equivalence classes of loops instead of individual loops as all loops belonging to the same equivalence class are considered equivalent upto homotopy.

## ∞-groupoid

So far we have:

1. Point in space
2. Loops over the point
3. Homotopies over loops
4. Fundamental group over homotopies

If we look at the derivation of homotopies, it seems evident we can continue to go up the ladder and define homotopies between homotopies and homotopies between homotopies between homotopies and so on till infinity.

![Figure 4: ∞-groupoid](/artwork/infty_groupoid.png)

Such a structure of infinite levels of homotopies with points followed by paths as base is called the _∞-groupoid_.

### Groupoid

To formally derive an ∞-groupoid, we start with a groupoid, which belongs to the family of groups.

A groupoid is a structure containing:

- A set $𝔽$
- A binary operation: `∙`

where:

1. `∙` is a partial function, i.e. it might not exist for every `x, y ∈ 𝔽`.
2. `∙` is associative, i.e. `x ∙ (y ∙ z) == (x ∙ y) ∙ z`
3. `∙` has an identity, i.e. `∃ i ∈ A, i ∙ i = i`
4. every object `x` has an inverse `x⁻¹`, such that `((x ⁻¹) ∙ x) == i`

```agda
  record IsGroupoid (_∙_ : ★ A) (x : A) (_⁻¹ : ♠ A) : Set (a ⊔ ℓ) where
    field
      isEquivalence     : IsEquivalence _==_
      ∙-cong            : Congruent₂ _∙_
      assoc             : Associative _∙_
      identity          : Identity x _∙_
      inverse           : Inverse x _⁻¹ _∙_

    open IsEquivalence isEquivalence public

    ∙-congˡ : LeftCongruent _∙_
    ∙-congˡ y==z = ∙-cong y==z rfl

    ∙-congʳ : RightCongruent _∙_
    ∙-congʳ y==z = ∙-cong rfl y==z

    identityˡ : LeftIdentity x _∙_
    identityˡ = fst identity

    identityʳ : RightIdentity x _∙_
    identityʳ = snd identity

    inverseˡ : LeftInverse x _⁻¹ _∙_
    inverseˡ = fst inverse

    inverseʳ : RightInverse x _⁻¹ _∙_
    inverseʳ = snd inverse

    open import Types.equational2
    open withCongruence _==_ _∙_ _⁻¹ rfl trans sym ∙-cong x public

    -- uniqueness of the inverses
    uniqueˡ-⁻¹ : ∀ α β → (α ∙ β) == x → α == (β ⁻¹)
    uniqueˡ-⁻¹ = assoc+id+invʳ⇒invˡ-unique assoc identity inverseʳ

    uniqueʳ-⁻¹ : ∀ α β → (α ∙ β) == x → β == (α ⁻¹)
    uniqueʳ-⁻¹ = assoc+id+invˡ⇒invʳ-unique assoc identity inverseˡ
```

Basically, the above structure is a group with partial function instead of total.

### ∞-groupoid

Formally, an infinity-groupoid (∞-groupoid) is a structure

- A set of objects `A`
- A set of morphisms or arrows between those objects
- A set of arrows



****
[Back to Contents](./contents.html)

