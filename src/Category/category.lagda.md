****
[Contents](contents.html)
[Previous](Algebra.introduction.html)
[Next](Category.functors.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Category](#category)
  - [Opposite Category](#opposite-category)
  - [Examples](#examples)
    - [Category of Sets](#category-of-sets)
    - [Category of Groups](#category-of-groups)
    - [Category of Rings](#category-of-rings)
    - [Category of Topological Spaces](#category-of-topological-spaces)
  - [Constructions of Categories](#constructions-of-categories)
    - [Product Category](#product-category)
    - [Free Category](#free-category)
- [Morphisms](#morphisms)
  - [Monomorphisms](#monomorphisms)
  - [Epimorphisms](#epimorphisms)
  - [Retraction](#retraction)
  - [Section](#section)
  - [Endomorphism](#endomorphism)
  - [Isomorphism](#isomorphism)
  - [Automorphism](#automorphism)

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

## Opposite Category

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

## Examples

We can use various mathematical structures to construct categories out of. When defining a category, we have to decide what our objects and our morphisms would be and how would the morphisms compose. This decision has to be taken in a way that the conditions of being a category are satisfied. We would then have a category of our chosen object.

### Category of Sets

A category of sets is the simplest of categories we can construct and the most intuitive to understand given we have been trained to think in terms of sets.

- Objects: Sets
- Morphisms: Total functions between sets
- Composition: Function composition

### Category of Groups

- Objects: Groups
- Morphisms: Group homomorphisms
- Composition: Composition of group homomorphisms

### Category of Rings

- Objects: Rings
- Morphisms: Ring homomorphisms
- Composition: Composition of ring homomorphisms

### Category of Topological Spaces

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

## Constructions of Categories

### Product Category

Given two (or more) categories, their cartesian product is also a category.

Given two categories ℂ and 𝔻, their product is a category with:
- Pairs (C, D) as objects such that C ∈ ℂ and D ∈ 𝔻
- (f, g) as morphisms where
  - $f : C_1 → C_2; C_i ∈ ℂ$
  - $g : D_1 → D_2; D_i ∈ 𝔻$
- composition of morphisms defined as $(f_1, g_1) ∘ (f_2, g_2) = (f_1 ∘ f_2, g_1 ∘ g_2)$
- identities  defined as $1_{(C, D)} = (1_C, 1_D)$

### Free Category

Free categories are a result of using a general pattern called "free constructions" for building categories. The idea of free objects in mathematics can be related to all types of objects with algebraic structure, and provides a general method of constructing objects using a set of "constructor" objects. The process of construction proceeeds as follows:

1. Take a set of objects to construct the free category with
2. Construct all possible combinations of these objects, in other words, the power set of the set of those objects. These form the algebraic object of interest
3. Define relations between every pair of objects according to the kind of algebraic object to construct

For free categories these rules become:

1. Consider a bunch of objects to be taken as generators
2. Construct the power set of these generators, these form the objects of the free category
3. Define morphisms between every pair of objects and all compositions of their morphisms, together they form the hom-set of the free category

# Morphisms

Morphisms are structure-preserving maps from one mathematical structure to another of the same type. They are a generalized notion that translates to group homomorphisms for groups, ring homomorphisms for rings, continuous maps for vector spaces and so on. In the context of category theory, these morphisms have to admit the properties of composition and associativity.

## Monomorphisms

A morphism $f : X → Y$ is called a Monomorphism if $f ∘ g_1 = f ∘ g_2$ implies $g_1 = g_2$ for all $g_1, g_2 : A → X$. A monomorphism is called "mono" in short and "monic" can be used as an adjective to describe such a morphism.

![Figure 1: Monomorphism](/artwork/monic.png)

## Epimorphisms

Epimorphisms are dual objects to monomorphisms. A morphism $f : X → Y$ is called an Epimorphism if $g_1 ∘ f = g_2 ∘ f$ implies $g_1 = g_2$ for all $g_1, g_2 : Y → A$. An Epimorphism is called "epi" in short and "epic" can be used as an adjective to describe such a morphism.

![Figure 2: Epimorphism](/artwork/epic.png)

## Retraction

A morphism $f: X → Y$ has a left inverse if there is a morphism $g: Y → X$ such that $g ∘ f = id_X$. The left inverse g is also called a retraction of f. Morphisms with left inverses are always monomorphisms, but the converse is not true in general; a monomorphism may fail to have a left inverse. If a retraction exists for a function f, it can also be expected to be injective.

## Section

A morphism $f: X → Y$ has a right inverse if there is a morphism $g: Y → X$ such that $f ∘ g = id_Y$. The right inverse g is also called a section of f. Morphisms having a right inverse are always epimorphisms, but the converse is not true in general, as an epimorphism may fail to have a right inverse. If a section exists for a function f, it can also be expected to be surjective.

## Endomorphism

Endomorphisms are morphisms with the same source and target, $f : X → X$.

## Isomorphism

A morphism $f : X → Y$ is called an isomorphism if there exists a unique morphism $g: Y → X$ such that $f ∘ g = id_Y$ and $g ∘ f = id_X$. If a morphism has both left-inverse and right-inverse, then the two inverses are equal, so f is an isomorphism, and g is called simply the inverse of f.

## Automorphism

An automorphism is both an endomorphism and an isomorphism.

---

[Categories](./Category.functors.html)
