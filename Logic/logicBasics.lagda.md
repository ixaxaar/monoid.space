****
[Contents](contents.html)
[Previous](Logic.introduction.html)
[Next](Logic.equality.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Constructing Boolean algebra using type theory](#constructing-boolean-algebra-using-type-theory)
  - [Objects of Logic](#objects-of-logic)
    - [Empty / False](#empty--false)
    - [Singleton / True](#singleton--true)
  - [Operations on these objects](#operations-on-these-objects)
    - [Negation or the logical `NOT`](#negation-or-the-logical-not)
    - [Product, conjunction `∧` or the logical `AND`](#product-conjunction-%E2%88%A7-or-the-logical-and)
    - [Co-product, disjunction or the logical `OR`](#co-product-disjunction-or-the-logical-or)
  - [Higher-order operations](#higher-order-operations)
    - [Implication](#implication)
    - [The exclusive or or `XOR`](#the-exclusive-or-or-xor)
    - [Absurd](#absurd)
    - [Contradiction](#contradiction)
    - [Contraposition](#contraposition)
    - [Boolean construction](#boolean-construction)
    - [Existential Quantification](#existential-quantification)
    - [Dependent proposition type](#dependent-proposition-type)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Constructing Boolean algebra using type theory

Here we look at constructing logic using type theory. Now, mostly all branches of mathematics involve two kinds of entities: objects and propositions about those objects. This very much corresponds to basic composition of programming languages - objects and their APIs.

```agda
module Logic.logicBasics where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
```

## Objects of Logic

### Empty / False

Type with no object - cannot ever create an object of this type. This makes it possible to define absurd functions, which map `⟂` to anything, as given nothing, one can create anything, or assuming any `False` statement can serve as a proof for anything, which is absurd.

```agda
data ⟂ : Set where
```

Absurd can imply anything, be it true or not. Thus, any statement can be proven using absurdity.

However, it is, we argue, impossible to create an object of absurd type (as `⟂` has no constructor) and hence these functions make no sense in the "real world", as in they can never be invoked. This is called the "absurd pattern".


### Singleton / True

Set with only one object: `True`.

```agda
data ⊤ : Set where
  singleton : ⊤
```

We also have a more standard representation of boolean objects, [Bool](./Types.dataStructures.html#boolean-type).

```agda
open import Lang.dataStructures using (Bool; true; false)
```

## Operations on these objects

### Negation or the logical `NOT`

We use the fact that a negation of a proposition `P` (to exist and hence be true) implies `¬ P` has to be false, `⟂`.

```agda
¬ : ∀ {a} → Set a → Set a
¬ P = P → ⟂
```

```agda
not : Bool → Bool
not true = false
not false = true
```

### Product, conjunction `∧` or the logical `AND`

The logic `AND` and `OR` are pretty straightforward for both representations:

```agda
data _∧_ (A B : Set) : Set where
  AND : A → B → A ∧ B

infixr 4 _∧_
```

```agda
_&&_ : Bool → Bool → Bool
true && x = x
false && x = false

infixr 4 _&&_
```

### Co-product, disjunction or the logical `OR`

```agda
data _∨_ (A B : Set) : Set where
  inj1 : A → A ∨ B
  inj2 : B → A ∨ B

infixr 4 _∨_
```

```agda
_||_ : Bool → Bool → Bool
true || x = true
false || x  = false

infixr 4 _||_
```

## Higher-order operations

These higher-order operations are built by composing the lower ones in various ways:

### Implication

Implication, or `if P then Q`, is derived from the well-known construction

$$
a ⟹ b = ¬ a ∨ b
$$

```agda
data _⟹_ (A B : Set) : Set where
  it⟹ : (¬ A) ∨ B → A ⟹ B
```

```agda
impl : Bool → Bool → Bool
impl x y = (not x) || y
```

Notice how the two implementations are different: `⟹` is constructive, whereas `impl` is computatational.

### The exclusive or or `XOR`

```agda
data _⨁_ (A B : Set) : Set where
  ⨁₁ : A → B → (A ∨ B) ∧ (¬ (A ∧ B)) → A ⨁ B
```

```agda
xor : Bool → Bool → Bool
xor x y = (x || y) && (not (x && y))
```

### Absurd

The absurd pattern for proving `Whatever`, we discussed [above](#empty--false):

```agda
⟂-elim : ∀ {w} {Whatever : Set w}
        → ⟂ → Whatever
⟂-elim ()
```

### Contradiction

A proposition `P` can always be true `⊤` if `¬ P` is always false `⟂`. If one were to assume a contradictory proposition `P`, one could prove anything as a contradiction makes `P` absurd. This is called as "ex falso quodlibet" or "from falsity, whatever you like". We can `⟂-elim` it in such a way to prove this:

```agda
contradiction : ∀ {p w} {P : Set p} {Whatever : Set w}
        → P
        → ¬ P
        → Whatever
contradiction p (¬p) = ⟂-elim (¬p p)
```

### Contraposition

Consider two propositions, `A` and `B`. Now if `A → B` is true, then `¬ A → ¬ B` will be true. In other words, if a statement `A` always implies another `B`, then `B` not being true would imply `A` not being true. This is called a contraposition and is proven in the following manner:

```agda
contrapos : ∀ {a b} {A : Set a}{B : Set b}
        → (A → B)
        → ¬ B → ¬ A
contrapos f ¬b a = contradiction (f a) ¬b
```

### Boolean construction

We can obviously go ahead now and implement the `if-then-else` semantic:

```agda
if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else y = x
if false then x else y = y
```

Note again that since this is a computational semantic, we provide implementation for only the concrete type `Bool`.

### Existential Quantification

Existential Quantification, or better known as "there exists" or `∃`, essential indicates if a proposition can exist:

```agda
data ∃ {A : Set} (P : A → Set) : Set where
  exists : {x : A}
        → P x
        → ∃ P
```

### Dependent proposition type

This is a dependent type, which creates propositions from a proposition family `P`:

```agda
∏ : {A : Set}(P : A -> Set) -> Set
∏ {A} P = (x : A) → P x
```

****
[Equality](./Logic.equality.html)
