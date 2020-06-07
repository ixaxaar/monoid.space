<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Topology](#topology)
- [Introduction](#introduction)
- [Open Sets](#open-sets)
- [Topological Space](#topological-space)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

****
[Contents](contents.html)
[Previous](AlgGeom.introduction.html)
[Next](./AlgGeom.space.html)

# Topology

```agda
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




****
[Spaces and Paths](./AlgGeom.topology.html)
