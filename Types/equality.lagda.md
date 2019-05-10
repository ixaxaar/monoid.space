<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Equalities](#equalities)
  - [Propositional Equality](#propositional-equality)
      - [Symmetry](#symmetry)
      - [Transitivity](#transitivity)
    - [Congruence: functions that preserve equality](#congruence-functions-that-preserve-equality)
    - [Substitution](#substitution)
- [Definitonal Equality](#definitonal-equality)
- [Relations, a deeper look](#relations-a-deeper-look)
  - [Equality](#equality)
  - [Types of relations](#types-of-relations)
    - [Nullary relations](#nullary-relations)
    - [Unary relations](#unary-relations)
    - [Binary relations](#binary-relations)
    - [Properties of binary relations](#properties-of-binary-relations)
  - [Properties of equality](#properties-of-equality)
- [Setoids](#setoids)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Equalities

```agda
module Types.equality where

open import Lang.dataStructures using (
  Bool; true; false;
  ⟂; ⊤; ℕ; List;
  one; two; three; four; five; six; seven; eight; nine; ten; zero; succ;
  _::_; [])

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

open import Types.functions using (_on_; flip)
```

As we previously mentioned, equality, in type theory, is itself a type. Hence the definiton of equality can be constructed for different types. There exists an equality by definiton as well. This results in two different kinds of equivalence relations and hence, kinds of equalities in type theory.

## Propositional Equality

In type theory, all proofs can be represented as a type. Propositional equality can be thought of as encapsulating the notion of "similarity", rather than strict equality. E.g. "roses" or "roads" hint at all roses or roads as being of the same kind but not exactly same, thus we define propositional equality over roses or roads which is different from hard equality. Propositional equality is a kind of equality which requires a proof, and hence the equality itself is also a type `∼`:

![equailty](./equailty.png)

```agda
infix 4 _∼_

data _∼_ {A : Set}(a : A) : {B : Set} → B → Set where
  same : a ∼ a
```

Reflexivity is defined with the definition of `∼` by the keyword `refl`, the others being:

#### Symmetry

```agda
symmetry : ∀ {A B}{a : A}{b : B}
  → a ∼ b
  → b ∼ a
symmetry same = same
```

#### Transitivity

```agda
transitivity : ∀ {A B C}{a : A}{b : B}{c : C}
  → a ∼ b
  → b ∼ c
  → a ∼ c
transitivity same p = p
```

### Congruence: functions that preserve equality

Functions that when applied to objects of a type, do not alter the operation of equality can be defined as:

```agda
congruence : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ∼ y
  → f x ∼ f y
congruence f same = same
```

### Substitution

If `a = b` and if `predicate a = true` ⟹ `predicate b = true`

```agda
substitution : ∀ {A : Set} {x y : A} (Predicate : A → Set)
  → x ∼ y
  → Predicate x
  → Predicate y
substitution Predicate same p = p
```

Finally, our table example:

```agda
data Table : Set where
  generic : Table
  specific : ℕ → Table

tableEqZero : generic ∼ generic
tableEqZero = same

tableEqThree : (specific three) ∼ (specific three)
tableEqThree = same
```

This, of course does not compile:

```haskell
tableEqNot : generic ∼ (specific three)
tableEqNot = same
```

Any relation which satisfies the above properties of `reflexivity`, `transitivity` and `symmetry` can be considered an equivalence relation and hence can judge a propositional equality.

# Definitonal Equality

Definitonal equality relates to the Agda compiler's own integrity check through which a statement is deemed true or correctly compiled. Hence every statemtent has its own notion of judgemental equality. This is in some way more fundamental than propositional equality as in it forms the very core of type theory's "judgement" of a `type(obj) == T`. The notion of definitonal equality also encompasses types that are isomorphic to each other e.g. `9 ≡ 3²`.

```agda
defEqual₁ : ℕ
defEqual₁ = seven

defEqual₂ : ℕ
defEqual₂ = seven
```

Here, `defEqual₁` and `defEqual₂` both are of type `ℕ` and hence definitionally equal is known to the compiler.


# Relations, a deeper look

We now present a more formal machinery for relations. We use [universe polymorphism](Types.universe.html#universe-polymorphism) throughout to develop this machinery.

## Equality

We first re-define propositional equality within the framework of universe polymorphism:

```agda
infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x
```

## Types of relations

### Nullary relations

Nullary relations are functions that can take any object and return an empty set `∅`:

```agda
¬  : ∀ {ℓ} → Set ℓ → Set ℓ
¬ P = P → ⟂
```

### Unary relations

In logic, a predicate can essentially be defined as a function that returns a binary value - whether the proposition that the predicate represents is true or false. In type theory, however, we define predicate in a different way. A predicate for us is a function that exists (and hence, is true):

```agda
Pred : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
Pred A ℓ = A → Set ℓ
```

The empty (or false) predicate becomes:

```agda
∅ : ∀ {a} {A : Set a} → Pred A lzero
∅ = λ _ → ⟂
```

The singleton predicate (constructor):

```agda
is_sameAs : ∀ {a} {A : Set a}
        → A
        → Pred A a
is x sameAs = x ≡_
```

```agda
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

### Properties of binary relations

We define implication between two relations as:

```agda
_⇒_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
        → REL A B ℓ₁
        → REL A B ℓ₂
        → Set _
P ⇒ Q = ∀ {i j} → P i j → Q i j
```

Two homogenous relations `Rel A ℓ₁` and `Rel B ℓ₂`, given a function `f : A → B` are equivalent if:

```agda
_=[_]⇒_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
          Rel A ℓ₁ → (A → B) → Rel B ℓ₂ → Set _
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

Finally, we define an equivalence relation for binary relations:

```agda
record IsEquivalence {a ℓ} {A : Set a}
                     (_≈_ : Rel A ℓ) : Set (a ⊔ ℓ) where
  field
    rfl   : Reflexive _≈_
    sym   : Symmetric _≈_
    trans : Transitive _≈_

  reflexive : _≡_ ⇒ _≈_
  reflexive refl = rfl
```

## Properties of equality

We use the new structures to re-define the properties of propositional equality.

```agda
module ≡-properties {a} {A : Set a} where
  sym-≡ : Symmetric {A = A} _≡_
  sym-≡ refl = refl

  trans-≡ : Transitive {A = A} _≡_
  trans-≡ refl p = p

cong-≡ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y : A}
  → x ≡ y
  → f x ≡ f y
cong-≡ f refl = refl

subs-≡ : ∀ {a} {A : Set a}{x y : A} (Predicate : A → Set)
  → x ≡ y
  → Predicate x
  → Predicate y
subs-≡ Predicate refl p = p
```

# Setoids

Equality, or specifically, equivalence is at the heart of mathematics. In order to build more complex structures, we introduce a new datatype, which essentially encapsulates any datatype and it's equivalence operation:

```agda
record Setoid c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Data          : Set c
    _≈_           : Rel Data ℓ
    isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public
```

Setoids are extensively used throughout agda's standard library, however, we chose to avoid them here to be more explicit.

****
[Back to Contents](./contents.html)
