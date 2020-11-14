****
[Contents](contents.html)
[Previous](Algebra.category.html)
[Next](Category.natural_transformation.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Functors](#functors)
- [Trivial Functors](#trivial-functors)
  - [Constant Functor](#constant-functor)
  - [Identity Functor](#identity-functor)
- [Covariance and Contravariance](#covariance-and-contravariance)
- [Opposite Functors](#opposite-functors)
- [Hom Functors](#hom-functors)
  - [Covariant Hom-Functor](#covariant-hom-functor)
  - [Contravariant Hom-Functor](#contravariant-hom-functor)
- [Bifunctors and multifunctors](#bifunctors-and-multifunctors)
- [Endofunctor](#endofunctor)
- [Diagonal Functor](#diagonal-functor)
- [Forgetful Functor](#forgetful-functor)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Functors

```agda
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Types.product
open import Types.relations
open import Types.equality
open import Category.category
open import Category.morphisms

module Category.functors where
```

Functors can be thought of as structure preserving maps or functions that operate on one category to produce another category, maintaining the categorical structure of the first category in the second category. Functors operate on both objects and morphisms of the first category.

Formally, let ℂ and 𝔻 be two categories, then a functor 𝔽 between them:

- Takes every object c ∈ ℂ to an object 𝔽(c) ∈ 𝔻
- Takes every morphism $f : c_1 → c_2$ ∈ ℂ to a morphism $𝔽(f) : 𝔽(c_1) → 𝔽(c_2)$ in 𝔻 such that:
  - $𝔽(id_c) = id_{𝔽(c)}$
  - $𝔽(g ∘ f) = 𝔽(g) ∘ 𝔽(f)$ for all $f : c_1 → c_2$ and $g : c_2 → c_3$ ∈ ℂ

Thus, functors preserve composition and identity morphisms of the source category in the target category.

# Trivial Functors
## Constant Functor
## Identity Functor

# Covariance and Contravariance

Covariant functors are the vanilla functors we discussed in the previous section.

Contravariant functors are similar to covariant functors except that the functor reverses the direction of arrows in the target category.

Formally, let ℂ and 𝔻 be two categories, then a contravariant functor 𝔽 between them:

- Takes every object c ∈ ℂ to an object 𝔽(c) ∈ 𝔻
- Takes every morphism $f : c_1 → c_2$ ∈ ℂ to a morphism $𝔽(f) : 𝔽(c_2) → 𝔽(c_1)$ in 𝔻 such that:
  - $𝔽(id_c) = id_{𝔽(c)}$
  - $𝔽(g ∘ f) = 𝔽(f) ∘ 𝔽(g)$ for all $f : c_1 → c_2$ and $g : c_2 → c_3$ ∈ ℂ

Contravariant functors thus produce opposite categories. They can also be thought of as covariant functors from $ℂ^{op} → 𝔻$ or as $ℂ → 𝔻^{op}$ depending upon which one is convenient for working with. Contravariant functors play a very important role in various fields of mathematics, the most mentionable ones being presheaves and sheaves in algebraic topology are contravariant functors with some extra structure.

# Opposite Functors

Every functor $𝔽 : ℂ → 𝔻$ induces the opposite functor $𝔽^{op} : ℂ^{op} → 𝔻^{op}$ such that $(𝔽^{op})^{op} = 𝔽$.

# Hom Functors

For a category ℂ, the set of all morphisms in ℂ is called the Hom-set. If we take any object A ∈ ℂ, then the functor that maps any object X ∈ ℂ to the set of morphisms from A to X, i.e. Hom(A, X), is called the covariant Hom-functor. Similarly, the functor that maps any object X in ℂ to the set of morphisms from X to A, i.e. Hom(X, A), is called a contravariant Hom-functor.

## Covariant Hom-Functor

For a category ℂ and a fixed object A ∈ ℂ, a covariant Hom-functor $Hom(A, −) : A → Set$:

- Maps each object X ∈ ℂ to the set of morphisms of ℂ, Hom(A, X)
- Maps each morphism $f : X → Y$ to the morphism $Hom(A, f) : Hom(A, X) → Hom(A, Y)$ where each h ∈ Hom(A, f) takes some g ∈ Hom(A, X) to $f ∘ g$

![Figure 1: Covariant hom functor](/artwork/covariant_hom_functor.png)

## Contravariant Hom-Functor

For a category ℂ and a fixed object A ∈ ℂ, a contravariant Hom-functor $Hom(−, B) : B → Set$:

- Maps each object X ∈ ℂ to the set of morphisms of ℂ, Hom(X, B)
- Maps each morphism $f : X → Y$ to the morphism $Hom(f, B) : Hom(X, B) → Hom(Y, B)$ where each h ∈ Hom(f, A) takes some g ∈ Hom(Y, B) to $g ∘ f$

![Figure 2: Contravariant hom functor](/artwork/contravariant_hom_functor.png)

# Bifunctors and multifunctors

We define categories of the form 𝔸×𝔹 which is a cartesian product of two categories 𝔸 and 𝔹 as Cartesian categories. Given two functors $𝔽 : 𝔸 → 𝕏$ and $𝔾 : 𝔹 → 𝕐$, we can define a functor on a product category 𝔸×𝔹 as the cartesian product of the individual functors 𝔽×𝔾. Such a functor is called a bifunctor. We can extend this notion to multifunctors.

# Endofunctor

# Diagonal Functor

# Forgetful Functor

---

[Natural Transformations](./Category.natural_transformation.html)
