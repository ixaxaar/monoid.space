<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Topology](#topology)
- [Introduction](#introduction)
- [Open Sets](#open-sets)
- [Topological Space](#topological-space)
- [Modeling Topology](#modeling-topology)
  - [Apartness](#apartness)
  - [Continuity](#continuity)
    - [Brouwer’s Continuity Principle](#brouwers-continuity-principle)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

****
[Contents](contents.html)
[Previous](AlgGeom.introduction.html)
[Next](./AlgGeom.space.html)

# Topology

```agda
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Lang.dataStructures
open import Logic.logicBasics using (if_then_else_)
open import Logic.decidability

open import Types.relations
open import Types.equality

module AlgTopos.topology where
```

# Introduction

The primary object of study in Topology is a "Topological Space". A Topological Space is a set of points with a notion of "near-ness" of these points. There is also a notion of neighborhoods of these points and a set of rules relating points and their neighborhoods.

# Open Sets

The concept of an open set is the fundamental building block of topology. An open set tries to generalize the concept of an interval on the real number line. In a one dimension real space, i.e. the infinite real number line, an open set is a subset of the real number line, not containing the end points.

```math
𝕏 : ∀ x ∈ ℝ, x > a ~\&~ x < b
```

This concept can be extended to 2 dimensional spaces, and we have a disk without a boundary:

```math
𝕏 : ∀ x, y ∈ ℝ, (x² + y²) < a
```

In 3-dimensions, we have an open sphere, i.e. a sphere without its boundary. For higher dimensions we get open n-spheres.


Open sets have a more general and abstract definition: any collection of sets can be called open, as long as the union of an arbitrary number of open sets is open, the intersection of a finite number of open sets is open, and the space itself is open. In other words, an open set is "closed" under finite unions and intersections.

If 𝕆 is a collection of open sets on a space 𝕏,

1. The empty set belongs to 𝕆
2. 𝕏 ∈ 𝕆
3. ∀ 𝕩ᵢ ∈ 𝕆, ⋃ 𝕩ᵢ ∈ 𝕆
3. ∀ 𝕩ᵢ ∈ 𝕆, ⋂ 𝕩ᵢ ∈ 𝕆

This broader definition makes open sets as general objects for studying not just geometrical objects, but also vastly different areas.

# Topological Space

A topological space is then defined as an odered pair (𝕏, τ), where 𝕏 is a set, and τ is a collection of subsets of 𝕏 such that all members of τ are open.

Examples:

- Given `X = {1, 2, 3, 4}`, the collection `τ = {{}, {1, 2, 3, 4}}` of only the two subsets of X required by the axioms forms a topology of X, the trivial topology (indiscrete topology).
- Given `X = {1, 2, 3, 4}`, the collection `τ = {{}, {2}, {1, 2}, {2, 3}, {1, 2, 3}, {1, 2, 3, 4}}` of six subsets of X forms another topology of X.
- Given `X = {1, 2, 3, 4}` and the collection `τ = P(X)` (the power set of X), (X, τ) is a topological space. τ is called the discrete topology.
- Given `X = ℤ`, the set of integers, the collection τ of all finite subsets of the integers plus ℤ itself is not a topology, because (for example) the union of all finite sets not containing zero is not finite but is also not all of ℤ, and so it cannot be in τ.
- n-dimensional Manifolds, differentiable, smooth spaces and pretty much any other kind of geometrical space is a topological space.

# Modeling Topology

Because of this fundamental definition of open sets, topology can be related to computation. And we can exploit that fact in order to implement topological concepts in Agda.

## Apartness

Consider the family of functions which produce sequences of natural numbers:

```math
Baire : ℕ \to ℕ
```

```agda
Baire : Set
Baire = ℕ → ℕ
```

No two of these kinds of functions can ever be compared by looking at their outputs in finite time without knowing what those functions are inside. In other words, their equivalences are not decidable.

However, given two Baire functions, we can come up with a notion of "apartness" which is *Semidecidable*. Being semidecidable or recursively enumerable implies that apartness can be decidable, even if it may take infinite time to determine it.

We start with defining equality for natural numbers:

```agda
infix 1 _⩵_

data _⩵_ : Rel ℕ lzero where
  z⩵n : ∀ {n}                 → n ⩵ n
  s⩵s : ∀ {m n} (m⩵n : m ⩵ n) → succ m ⩵ succ n
```

Note that if we were to define apartness in a computational manner, we would have a condition where we would never terminate:

```haskell
infix 1 _==_

_==_ : ℕ → ℕ → Bool
zero == x = false
succ y == succ x = y == x
succ x == zero = false

Apartness1 : ℕ → Baire → Baire → Bool
Apartness1 n x y = if ((x n) == (y n)) then (Apartness1 (succ n) x y) else false

Apartness : Baire → Baire → Bool
Apartness x y = if ((x zero) == (y zero)) then (Apartness1 (succ zero) x y) else false
```

Produces:

```haskell
Termination checking failed for the following functions:
  Apartness1
Problematic calls:
  Apartness1 (succ n) x y
```

In the world of type theory, this failure of reaching termination reveals itself in a different form − it would be impossible to create an object of type `Apartness`.

```agda
record Apartness (x y : Baire) : Set where
  field
    isApart : ∀ n → (x n) ⩵ (y n)

record ApartnessOver (x y : Baire) (f : ℕ → ℕ) : Set where
  field
    isApartOver : ∀ n → (x n) − (y n) ⩵ f n
```

Consider the Baire functions

```agda
b1 : Baire
b1 x = x × four

b2 : Baire
b2 x = x × (two × two)

b3 : Baire
b3 x = (x × seven) × nine
```

The apart function for b1 and b2:

```agda
b1b2areApart : Apartness b1 b2
b1b2areApart = record { isApart = λ n → z⩵n }
```

Whereas for b1 and b3, we would not be able to create a type `Apartness b1 b3`.

## Continuity

The standard definition of a continuous function is a function that does not have any abrupt changes in value, known as discontinuities. More precisely, sufficiently small changes in the input of a continuous function result in arbitrarily small changes in its output.

### Brouwer’s Continuity Principle




A function `f : A → B` is called "continuous" if it can be definable, i.e. foes not involve absurdities like ⟂. This definition of continuity

****
[Spaces and Paths](./AlgGeom.topology.html)

