****
[Contents](contents.html)
[Previous](Category.yoneda.html)
[Next](Category.adjunctions.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Limits](#limits)
  - [Diagram](#diagram)
    - [Indexed Category](#indexed-category)
  - [Limit](#limit)
    - [Terminal Object](#terminal-object)
    - [Product](#product)
    - [Equalizer](#equalizer)
    - [Pullback](#pullback)
  - [Colimits](#colimits)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Limits

```agda
module Category.limits where
```

Limits are an abstract structure that captures and generalizes concepts such as products and coproducts, pullbacks and equalizers.

## Diagram

An indexed family of sets is a collection of objects where each object is labeled with an object from an index set. For example, say X is a set of $x_i$'s with each $x_i$ labeled with an integer $i$, so $x_1, x_2 ... x_n ∈ X$. Another way to look at them is to say an indexed family is a function which when given an index returns a member of X, i.e. it is a function that takes an $i$ and returns an $x_i$: $f : i → x_i$.

A diagram is a categorical analogue of indexed families. Informally, a diagram in a category ℂ consists of some objects of ℂ connected by some morphisms of ℂ all indexed by a fixed category.

### Indexed Category

Formally, an indexed category ℂ indexed over a category $\mathcal{S}$ is defined by a functor:

$$
ℂ : \mathcal{S}^{op} → Cat
$$

where `Cat` is the category of categories (a 2-category) and $\mathcal{S}$ can be thought of as the analogue of the set `i` for indexed sets. If $\mathcal{S}$ has a terminal object `*` we think of $ℂ$ as the underlying ordinary category of the $\mathcal{S}$-indexed category ℂ.

A diagram takes an indexed category $\mathcal{J}$ and maps it to a category ℂ:

$D : \mathcal{J} → ℂ$

 The diagram D is thought of as indexing a collection of objects and morphisms in C patterned on J, which is usually a very small category. This permits us to single out and study repeating patterns or subgraphs of a category. Diagrams permit further structures:

 1. The category of $\mathcal{J}$-shaped diagrams in ℂ is the functor category $Funct(\mathcal{J},ℂ)$.
 2. A diagram $D : \mathcal{J} → ℂ$ is constant if it is a constant functor.
 3. A cone over a diagram $D : \mathcal{J} → ℂ$ with tip of the cone an arbitrary object C ∈ ℂ is a natural transformation from the constant diagram $Const : \mathcal{J} → ℂ$ to $D$, i.e. $Cone : Const ⟹ D$.
 4. A co-cone is the dual of cone $CoCone : D ⟹ Const$.

## Limit

The limit of a diagram D, denoted by $\lim D$ is a cone (A, η) to D such that for every other cone (B, ψ) there exists a unique morphism $u : A → B$ such that $η_X ∘ u = ψ_X$ for all X in D. Limits are thus a universal construction. Diagrams may have limits, when they do the limits are essentially unique. This category theoretic notion does represent the same notion in analysis (limits in the context of calculus).

Let $F : D^{op} \to C$ be a functor. If the limit $\lim F \in C$ of F exist, then it singles out a special cone given by the composite morphism

$*→*↦Id limFHom C(limF,limF)→≃Hom(pt,Hom(limF,F(−)))$

where the first morphism picks the identity morphism on limF\lim F and the second one is the defining bijection of a limit as above.

The cone is called the universal cone over F.

Here are some important examples of limits, classified by the shape of the diagram:

- A limit of the empty diagram is a terminal object.
- A limit of a diagram consisting of two (or more) objects and no nontrivial morphisms is their product.
- A limit of a cospan is a pullback.
- A limit of a pair (or more) of parallel morphisms is an equalizer.
- A limit over a finite category is a finite limit.
- Another important “shape” of limits are those that give rise to ends.


### Terminal Object

### Product

### Equalizer

### Pullback

## Colimits

---

[Yoneda Lemma](./Category.adjunctions.html)

