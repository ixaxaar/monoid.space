****
[Contents](contents.html)
[Previous](Algebra.category.html)
[Next](Category.natural_transformation.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Functors](#functors)
- [Covariance and Contravariance](#covariance-and-contravariance)
- [Opposite Functors](#opposite-functors)
- [Hom Functors](#hom-functors)
- [Bifunctors and multifunctors](#bifunctors-and-multifunctors)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Functors

```agda
module Category.functors where
```

Functors can be thought of as structure preserving maps or functions that operate on one category to produce another category, maintaining the categorical structure of the first category in the second category. Functors operate on both objects and morphisms of the first category.

Formally, let ℂ and 𝔻 be two categories, then a functor 𝔽 between them:

- Takes every object c ∈ ℂ to an object 𝔽(c) ∈ 𝔻
- Takes every morphism $f : c_1 → c_2$ ∈ ℂ to a morphism $𝔽(f) : 𝔽(c_1) → 𝔽(c_2)$ in 𝔻 such that:
  - $𝔽(id_c) = id_{𝔽(c)}$
  - $𝔽(g ∘ f) = 𝔽(g) ∘ 𝔽(f)$ for all $f : c_1 → c_2$ and $g : c_2 → c_3$ ∈ ℂ

Thus, functors preserve composition and identity morphisms of the source category in the target category.

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

# Hom Functors

# Bifunctors and multifunctors

---

[Natural Transformations](./Category.natural_transformation.html)
