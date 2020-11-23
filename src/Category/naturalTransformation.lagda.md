****
[Contents](contents.html)
[Previous](Category.functors.html)
[Next](Category.yonedaLemma.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Natural Transformations](#natural-transformations)
  - [Commutative Diagrams](#commutative-diagrams)
  - [Composition](#composition)
  - [Functor Categories](#functor-categories)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Natural Transformations

```agda
module Category.naturalTransformation where
```

## Commutative Diagrams

Commutative diagrams are a great tool widely used in category to pictorially depict constraints rather than using mathematical equations. These diagrams are directed graphs with each node representing mathematical objects and the arrows between them represent morphisms.

A commutative diagram often consists of three parts:

- objects (also known as vertices)
- morphisms (also known as arrows or edges)
- paths or composites (that compose these morphisms)

A diagram is said to be commutative (or to commute) when if any two paths that connect the same two objects (no matter how many hops each path may have) arrive at the same result - it does not matter which path one takes to arrive at the end.

##️ Natural Transformations

Natural transformations are structure preserving maps between functors. Just as a functor is a morphism between categories, a natural transformation is a morphism between two functors. Since it is at a higher level than functors, it can also be called a 2-morphism.

![Figure 1: Natural Transformation](/artwork/natural_transformation.png)

Given categories ℂ and 𝔻 and functors $F, G : ℂ → 𝔻$ and for some $f : x → y$, a natural transformation $α : F → G$ ensures the following diagram is satisfied (the following diagram "commutes"):

![Figure 2: Natural Transformation Commutative Diagram](/artwork/natural_transformation_diagram.png)

## Composition

Natural transformations can either be composed horizontally or vertically:

![Figure 3: Horizontal Composition](/artwork/natural_transformation_composition.png)

![Figure 4: Vertical Composition](/artwork/natural_transformation_composition_vertical.png)

Both kinds of composition allows for the associativity law and identity natural transformations.

## Functor Categories

As we have seen above, composition of natural transformations follows all the laws that morphisms follow in a category. We can take advantage of that fact and define a category of functors:

Given two categories ℂ and 𝔻, we can define a category of functors with:
- Functors $F_i : ℂ → 𝔻$ as objects
- Natural transformations $η : F_i → F_j$ as morphisms

The natural transformations between ℂ and 𝔻 which are isomorphisms are also called Natural Isomorphisms.

The above definition of functor categories take into account only vertical compositions. We can also define a more general kind of functor categories, also called a 2-category:

Given a bunch of categories $𝕔_i$, we can define a 2-category with:
- categories $𝕔_i$ as objects
- Functors between $𝕔_i$ as morphisms: $F_{ij} : 𝕔_i → 𝕔_j$
- Natural transformations between functors as 2-morphisms: $η : F_{ij} → F'_{ij}$ and $γ : F_{ij} → G_{jk}$

---

[Yoneda Lemma](./Category.yonedaLemma.html)

