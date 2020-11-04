****
[Contents](contents.html)
[Previous](Algebra.introduction.html)
[Next](Category.functors.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Category](#category)
- [Opposite Category](#opposite-category)
- [Some useful categories](#some-useful-categories)
  - [Category of Sets](#category-of-sets)
  - [Category of Groups](#category-of-groups)
  - [Category of Rings](#category-of-rings)
  - [Category of Topological Spaces](#category-of-topological-spaces)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Category

```agda
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Types.product
open import Types.relations
open import Types.equality

module Category.category where
```

A category is the object of study in category theory. It can be thought of being a bunch of objects, which are associated by a bunch of arrows between those objects, with the arrows being composable and each object having unit arrows. This minimal structure ensures a multitude of object types studied in mathematics can fit the description.

A category ℂ consists of:

1. A collection of objects $x \in obj(ℂ)$
2. A collection of morphisms between those objects $hom(𝕔) = \{ f : a → b : a,b ∈ ℂ \}$, called a "hom" set

such that:

1. Morphisms compose:

If
$$f : a → b, g : b → c$$
then
$$g ∘ f : a → c$$

2. Morphisms are associative:

$$If~~ f : a → b,~ g : b → c ~~and~~ h : c → d ~~then~~ h ∘ (g ∘ f) = (h ∘ g) ∘ f$$

3. Morphisms have identities: For every object x, there exists a morphism $1ₓ : x → x$ called the identity morphism for x, such that for every morphism $f : a → x$ and every morphism $g : x → b$, we have $1ₓ ∘ f = f$ and $g ∘ 1ₓ = g$.

```agda
record Category (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where
  infix  4 _≈_ _⇒_
  infixr 9 _∘_

  field
    Obj : Set o                     -- objects
    _⇒_ : Rel Obj ℓ                 -- morphism
    _≈_ : ∀ {A B} → Rel (A ⇒ B) e   -- equivalence of morphisms
    id  : ∀ {A} → (A ⇒ A)           -- identity

    -- composition of morphisms
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

    -- laws
    -- satisfy associativity
    assoc     : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    -- satisfy identity
    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
    -- has an equivalence for morphisms
    equiv     : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
    -- composition is congruent on equivalence
    ∘-resp-≈  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i
```

# Opposite Category

The machinery of category theory also admits a duality, like an object and its mirror image. The opposite or dual of a category $ℂ$, denoted by $ℂᴼᵖ$, is the same category, but with all morphisms in the opposite direction. All laws and machinery of category theory have their dual versions.

```agda
record Categoryᴼᵖ (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where
  infix  4 _≈_ _⇒_
  infixr 9 _∘_

  field
    Obj : Set o                     -- objects
    _⇒_ : Rel Obj ℓ                 -- morphism
    _≈_ : ∀ {A B} → Rel (B ⇒ A) e   -- equivalence of morphisms
    id  : ∀ {A} → (A ⇒ A)           -- identity

    -- composition of morphisms
    _∘_ : ∀ {A B C} → (B ⇒ A) → (C ⇒ B) → (C ⇒ A)

    -- laws
    -- satisfy associativity
    assoc     : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f
    -- satisfy identity
    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
    -- has an equivalence for morphisms
    equiv     : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
    -- composition is congruent on equivalence
    ∘-resp-≈  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → g ≈ i → f ≈ h → g ∘ f ≈ i ∘ h
```

# Some useful categories

We can use various mathematical structures to construct categories out of. When defining a category, we have to decide what our objects and our morphisms would be and how would the morphisms compose. This decision has to be taken in a way that the conditions of being a category are satisfied. We would then have a category of our chosen object.

## Category of Sets

A category of sets is the simplest of categories we can construct and the most intuitive to understand given we have been trained to think in terms of sets.

- Objects: Sets
- Morphisms: Total functions between sets
- Composition: Function composition

## Category of Groups

- Objects: Groups
- Morphisms: Group homomorphisms
- Composition: Composition of group homomorphisms

## Category of Rings

- Objects: Rings
- Morphisms: Ring homomorphisms
- Composition: Composition of ring homomorphisms

## Category of Topological Spaces

- Objects: Topological Spaces
- Morphisms: Continuous maps/functions between spaces
- Composition: Composition of continuous maps

Here are some other examples:

| Category | Objects | Morphisms |
| --- | --- | --- |
| Set | sets | total functions |
| Group | groups | group homomorphisms |
| Top | topological spaces | continuous functions |
| Vectₖ | vector spaces over field K | linear transformations |
| Poset | partially ordered sets | order-preserving functions |
| TopVect | topological vector spaces | continuous linear maps |
| 𝕄 | differentiable manifolds | differentiable maps |
| Banach spaces | open subsets of banach spaces | differentiable maps |
| 𝕍 | vector bundles | vector bundle maps |

There are in fact infinitely many more and so we are going to move along now.

---

[Categories](./Category.functors.html)
