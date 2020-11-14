****
[Contents](contents.html)
[Previous](Category.category.html)
[Next](Category.functors.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Morphisms](#morphisms)
  - [Monomorphisms](#monomorphisms)
  - [Epimorphisms](#epimorphisms)
  - [Retraction](#retraction)
  - [Section](#section)
  - [Endomorphism](#endomorphism)
  - [Isomorphism](#isomorphism)
  - [Automorphism](#automorphism)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Morphisms

```agda
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Types.product
open import Types.relations
open import Types.equality
open import Category.category

module Category.morphisms where
```

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

[Functors](./Category.functors.html)
