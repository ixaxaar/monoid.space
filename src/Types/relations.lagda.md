****
[Contents](contents.html)
[Previous](Types.universe.html)
[Next](Types.equality.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Relations](#relations)
    - [Types of relations](#types-of-relations)
    - [Nullary relations](#nullary-relations)
    - [Unary relations](#unary-relations)
    - [Binary relations](#binary-relations)
      - [Properties of binary relations](#properties-of-binary-relations)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Relations

```agda
module Types.relations where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Lang.dataStructures using (
  Bool; true; false;
  ⟂; ⊤; ℕ; List;
  one; two; three; four; five; six; seven; eight; nine; ten; zero; succ; _+_;
  _::_; [])
open import Types.functions using (_on_; flip)
```

Relations can be defined as properties that assign truth values to finite tuples of elements. In other words, a relation is a function that accepts a finite set of arguments to produce a truth value. A binary relation would output a truth value given two objects, similarly a unary relation would apply on a single object to output a truth value. This can be generalized to k-ary relations.

In type theory, since relations are also types and "truth values" of a proposition is replaced by existence or belonging to the universe of all types, one can think of relations as functions that take n-tuples as input and return some  object of type `Set1` - the set of all `Set`s.

### Types of relations

### Nullary relations

Nullary relations are functions that can take any object and return an empty set `∅`:

```agda
infix 3 ¬_

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ P = P → ⟂
```

### Unary relations

In logic, a predicate can essentially be defined as a function that returns a binary value - whether the proposition that the predicate represents is true or false. In type theory, however, we define predicate in a different way. A predicate for us is a function that exists (and hence, is true):

```agda
Pred : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
Pred A ℓ = A → Set ℓ
```

Here, a predicate `P : Pred A ℓ` can be seen as a subset of A containing all the elements of A that satisfy property P.

Membership of objects of `A` in `P` can be defined as:

```agda
infix 4 _∈_ _∉_

_∈_ : ∀ {a ℓ} {A : Set a} → A → Pred A ℓ → Set _
x ∈ P = P x

_∉_ : ∀ {a ℓ} {A : Set a} → A → Pred A ℓ → Set _
x ∉ P = ¬ (x ∈ P)
```

The empty (or false) predicate becomes:

```agda
∅ : ∀ {a} {A : Set a} → Pred A lzero
∅ = λ _ → ⟂
```

The singleton predicate (constructor):

```lagda
is_sameAs : ∀ {a} {A : Set a}
        → A
        → Pred A a
is x sameAs = x ≡_
```

```lagda
equal? : is six sameAs (succ five)
equal? = refl
```

### Binary relations

A heterogeneous binary relation is defined as:

```agda
REL : ∀ {a b} → Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ lsuc ℓ)
REL A B ℓ = A → B → Set ℓ
```

and a homogenous one as:

```agda
Rel : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
Rel A ℓ = REL A A ℓ
```

#### Properties of binary relations

In type theory, an implication $ A ⟹ B $ is just a function type $ f: A → B $, and if `f` exists, the implication does too. We define implication between two relations in agda as:

```agda
_⇒_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
        → REL A B ℓ₁
        → REL A B ℓ₂
        → Set _
P ⇒ Q = ∀ {i j} → P i j → Q i j
```

A function `f : A → B` is invariant to two homogenous relations `Rel A ℓ₁` and `Rel B ℓ₂` if $ ∀ x, y ∈ A ~and~ f(x), f(y) ∈ B, f(Rel x y) ⟹ (Rel f(x) f(y)) $:

```agda
_=[_]⇒_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
          → Rel A ℓ₁
          → (A → B)
          → Rel B ℓ₂
          → Set _
P =[ f ]⇒ Q = P ⇒ (Q on f)
```

A function `f` preserves an underlying relation while operating on a datatype if:

```agda
_Preserves_⟶_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
        → (A → B)
        → Rel A ℓ₁
        → Rel B ℓ₂
        → Set _
f Preserves P ⟶ Q = P =[ f ]⇒ Q
```

Similarly, a binary operation `_+_` preserves the underlying relation if:

```agda
_Preserves₂_⟶_⟶_ : ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} {C : Set c}
        → (A → B → C)
        → Rel A ℓ₁
        → Rel B ℓ₂
        → Rel C ℓ₃
        → Set _
_+_ Preserves₂ P ⟶ Q ⟶ R = ∀ {x y u v} → P x y → Q u v → R (x + u) (y + v)
```

Properties of binary relations:

```agda
Reflexive : ∀ {a ℓ} {A : Set a}
        → Rel A ℓ
        → Set _
Reflexive _∼_ = ∀ {x} → x ∼ x
```

```agda
Sym : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
        → REL A B ℓ₁
        → REL B A ℓ₂
        → Set _
Sym P Q = P ⇒ flip Q

Symmetric : ∀ {a ℓ} {A : Set a}
        → Rel A ℓ
        → Set _
Symmetric _∼_ = Sym _∼_ _∼_
```

```agda
Trans : ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} {C : Set c}
        → REL A B ℓ₁
        → REL B C ℓ₂
        → REL A C ℓ₃
        → Set _
Trans P Q R = ∀ {i j k} → P i j → Q j k → R i k

Transitive : ∀ {a ℓ} {A : Set a}
        → Rel A ℓ
        → Set _
Transitive _∼_ = Trans _∼_ _∼_ _∼_
```

****
[Equality](./Types.equality.html)
