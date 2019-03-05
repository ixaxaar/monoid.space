<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Equivalence](#equivalence)
- [Implication](#implication)
- [Preservation](#preservation)
- [Laws](#laws)
  - [Reflexivity](#reflexivity)
  - [Symmetric](#symmetric)
  - [Transitive](#transitive)
  - [Respect](#respect)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Equivalence

```agda
module Algebra.equality where

open import Types.typeBasics using (Σ; _,_)

open import Algebra.introduction

open import Level
```

We start our algebraic machinery with some definitions of binary relations, with universe levels. Homogenous binary relations can be defined as:

```agda
REL : ∀ {a b}
        → Set a
        → Set b
        → (ℓ : Level)
        → Set (a ⊔ b ⊔ suc ℓ)
REL A B ℓ = A → B → Set ℓ
```

and homogenous ones:

```agda
Rel : ∀ {a}
        → Set a
        → (ℓ : Level)
        → Set (a ⊔ suc ℓ)
Rel A ℓ = REL A A ℓ
```

# Implication

```agda
_⇒_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
      → REL A B ℓ₁
      → REL A B ℓ₂
      → Set _
P ⇒ Q = ∀ {i j} → P i j → Q i j
```

```agda
_=[_]⇒_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
        → Rel A ℓ₁
        → (A → B)
        → Rel B ℓ₂
        → Set _
P =[ f ]⇒ Q = P ⇒ (Q on f)
```

# Preservation

What do we mean when we say a structure is "preserved"? For any function `f`, two objects `a` and `b`,

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

# Laws

## Reflexivity

```agda
Reflexive : ∀ {a ℓ} {A : Set a}
  → Rel A ℓ
  → Set _
Reflexive _∼_ = ∀ {x} → x ∼ x
```

## Symmetric

```agda
flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c}
        → ((x : A) (y : B) → C x y)
        → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y

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

## Transitive

```agda
Trans : ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} {C : Set c}
        → REL A B ℓ₁
        → REL B C ℓ₂
        → REL A C ℓ₃
        → Set _
Trans P Q R = ∀ {i j k} → P i j → Q j k → R i k

Transitive : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Transitive _∼_ = Trans _∼_ _∼_ _∼_
```

## Respect

```agda
_Respects_ : ∀ {a ℓ₁ ℓ₂} {A : Set a}
        → (A → Set ℓ₁)
        → Rel A ℓ₂
        → Set _
P Respects _∼_ = ∀ {x y} → x ∼ y → P x → P y

_Respectsʳ_ : ∀ {a ℓ₁ ℓ₂} {A : Set a}
        → Rel A ℓ₁
        → Rel A ℓ₂
        → Set _
P Respectsʳ _∼_ = ∀ {x} → (P x) Respects _∼_

_Respectsˡ_ : ∀ {a ℓ₁ ℓ₂} {A : Set a}
        → Rel A ℓ₁
        → Rel A ℓ₂
        → Set _
P Respectsˡ _∼_ = ∀ {y} → (flip P y) Respects _∼_

_Respects₂_ : ∀ {a ℓ₁ ℓ₂} {A : Set a}
        → Rel A ℓ₁
        → Rel A ℓ₂
        → Set _
P Respects₂ _∼_ = (P Respectsʳ _∼_) × (P Respectsˡ _∼_)
```
