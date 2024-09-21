****
[Contents](contents.html)
[Previous](Logic.logicBasics.html)
[Next](Logic.laws.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Equality](#equality)
  - [Properties of Equivalence Relations](#properties-of-equivalence-relations)
    - [Reflexive](#reflexive)
    - [Symmetric](#symmetric)
    - [Transitive](#transitive)
    - [Congruent](#congruent)
    - [Substitutive](#substitutive)
  - [Equivalence relation](#equivalence-relation)
- [Logical Equivalence](#logical-equivalence)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Equality

```agda
module Logic.equality where

open import Logic.logicBasics using (¬; not; xor; ⟂; ⊤; singleton)
open import Lang.dataStructures using (Bool; true; false)
```

We start with the definition of a binary relation:

```agda
Rel : Set → Set1
Rel A = A → A → Set
```

Equality, or an equivalence, is the most basic comparison that can be performed between two objects. Let us first see how equality (and inequality) looks like for logic:

```agda
data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)
```

Equality can also be derived as a negation of XOR:

$$
a \equiv b ~is~ ~True~ \implies ¬ (a \bigoplus b) ~is~ True
$$

```agda
equal? : Bool → Bool → Bool
equal? a b = not (xor a b)
```

The laws of equality are same as what we saw earlier in [equality](Types.equality.html). However, we derive the the same laws without universe polymorphism:

## Properties of Equivalence Relations

Relations can conform to certain properties, which later come in handy for classifying relations and building a lot of mathematical structure.

### Reflexive

A reflexive relation is one where $$ x ∙ y = y ∙ x $$

```agda
reflexive : {A : Set}
  → Rel A
  → Set
reflexive {A} _★_ = (x : A) → x ★ x
```

### Symmetric

A symmetric relation is one where $$ x ∙ y ⟹ y ∙ x $$

```agda
symmetric : {A : Set} → Rel A → Set
symmetric {A} _★_  = (x y : A)
  → x ★ y
  → y ★ x
```

### Transitive

A transitive relation is one where $$ x ∙ y, y ∙ z ~then~ z ∙ x $$

```agda
transitive : {A : Set} → Rel A → Set
transitive {A} _★_ = (x y z : A)
  → x ★ y
  → y ★ z
  → x ★ z
```

### Congruent

A congruent relation is one where a function $$ x ∙ y ⟹ f(x) ∙ f(y) $$ or the function `f` preserves the relation.

```agda
congruent : {A : Set} → Rel A → Set
congruent {A} _★_ = (f : A → A)(x y : A)
  → x ★ y
  → f x ★ f y
```

### Substitutive

A substitutive relation is one where $$ x ∙ y ~and~ (predicate~ y) = ⊤ ⟹ (predicate~ x) = ⊤ $$

```lagda
substitutive : {A : Set} → Rel A → Set1
substitutive {A} _★_ = (P : A → Set)(x y : A)
  → x ★ y
  → P x
  → P y
```

## Equivalence relation

```agda
record Equivalence (A : Set) : Set1 where
  field
    _==_  : Rel A
    rfl   : reflexive _==_
    sym   : symmetric _==_
    trans : transitive _==_
```

# Logical Equivalence

Note, the only difference here is that each law applies to the same datatype, be it `⟂`, `⊤` or `Bool`.

```agda
symm : {A : Set} {x y : A}
        → x ≡ y
        → y ≡ x
symm {A} refl = refl
```

```agda
trans : {A : Set} {x y z : A}
        → x ≡ y
        → y ≡ z
        → x ≡ z
trans {A} refl a = a
```

Let us fit the above proofs of the properties of the relation `≡` to prove an equivalence relation:

```agda
Equiv : {A : Set} → Equivalence A
Equiv = record
  {
    _==_  = _≡_
    ; rfl   = \x      → refl
    ; sym   = \x y    → symm
    ; trans = \x y z  → trans
  }
```

To see that this applies to a `singleton`:

```agda
refl⊤ : singleton ≡ singleton
refl⊤  = Equivalence.rfl Equiv singleton

sym⊤ : singleton ≡ singleton → singleton ≡ singleton
sym⊤   = Equivalence.sym Equiv singleton singleton

trans⊤ : singleton ≡ singleton → singleton ≡ singleton → singleton ≡ singleton
trans⊤ = Equivalence.trans Equiv singleton singleton singleton
```

We cannot, however, verify this for `⟂` explicitly as we cannot produce an object that does not exist / does not have a constructor.

Inequality `≢` cannot serve as an equivalence relation as reflexivity and transitivity cannot be satisfied.

****
[Laws of Logic](./Logic.laws.html)

