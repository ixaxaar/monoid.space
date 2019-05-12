<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Equational Reasoning](#equational-reasoning)
  - [Trivial example](#trivial-example)
  - [Equational Reasoning over equivalence relations](#equational-reasoning-over-equivalence-relations)
  - [Some Proofs using equational reasoning](#some-proofs-using-equational-reasoning)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->



# Equational Reasoning

We now look at constructing a language or algebra atop a given relation and some of its properties. This serves as a nicer way of proving things by application of relations such as chains of transitivity.

```agda
{-# OPTIONS --without-K #-}

module Algebra.equational where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Types.equality
open import Types.typeBasics using (Σ; _,_)
```

## Trivial example

Given an equivalence relation `_≡_`, we have reflexivity, transitivity and symmetry to apply around. We can perform algebra on terms like `a ≡ b` using a combination of these laws, e.g. we could chain transitivity bounded by reflexivity into chains looking like:

`refl - transitive - transitive - transitive - refl`

This provides a more convenient way of writing proofs similar to how we write them more naturally on paper.

We define a trivial example of an equational reasoning module here:

```agda
module ≡-Reasoning {a ℓ} {A : Set a} (_≡_ : Rel A ℓ) (Eq : IsEquivalence _≡_) where
  open IsEquivalence Eq

  infix  3 _∎
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  1 begin_

  begin_ : ∀{x y : A} → x ≡ y → x ≡ y
  begin_ x≡y = x≡y

  _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A) → x ≡ x
  _∎ _ = rfl

----
```

We could use this to, say prove transitivity and commutativity of addition of natural numbers:

```agda
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
m + zero   = m
m + succ n = succ (m + n)
```

We can now prove transitivity of `+`:

```agda
module +-properties {ℓ} (_≡_ : Rel ℕ ℓ) (Eq : IsEquivalence _≡_) where
  open ≡-Reasoning _≡_ Eq public
  open IsEquivalence Eq public

  trans-+ : {x y z : ℕ} → x ≡ y → y ≡ z → x ≡ z
  trans-+ {x} {y} {z} x≡y y≡z = begin
    x ≡⟨ x≡y ⟩
    y ≡⟨ y≡z ⟩
    z ∎
```

<!-- To prove the law of commutativity of `+`, we need some properties of equality, like congruence `cong-≡`:

```lll
  open import Algebra.operations _≡_

  +-identityˡ : LeftIdentity zero _+_
  +-identityˡ _ = refl
```

```lll
  comm+ : ∀ {x, y} → x + y ≡ y + x
  comm+ x zero =
```

  comm+ x (succ y) = begin
    succ (x + y) ≡⟨ succ (sym x y) ⟩
    succ (y + x) ≡⟨ rfl  ⟩
    (succ y) + x ∎
 -->

We now define a more complex version where there is symmetry in equivalence preservation, unlike the previous naive version where it is only covariant, capturing the commutativity of the equivalence relation.

## Equational Reasoning over equivalence relations

```agda
module ★-reasoning
  {a ℓ}
  {A : Set a}
  (_∼_ : Rel A ℓ)
  (reflexive : Reflexive _∼_)
  (trans : Transitive _∼_)
  where

  infix  4 _IsRelatedTo_
  infix  3 _∎
  infixr 2 _∼⟨_⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_ _≡⟨⟩_
  infix  1 begin_
```

We start with a vague notion of being related to:

```agda
  data _IsRelatedTo_ (x y : A) : Set (a ⊔ ℓ) where
    relTo : (x∼y : x ∼ y) → x IsRelatedTo y
```

we concretize the fact of being related to into a `begin` statement, this forms the basis or starting point of any reasoning sequence.

```agda
  begin_ : ∀ {x y} → x IsRelatedTo y → x ∼ y
  begin relTo x∼y = x∼y
```

chaining transitivity:

```agda
  _∼⟨_⟩_ : ∀ x {y z} → x ∼ y → y IsRelatedTo z → x IsRelatedTo z
  _ ∼⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z)
```

covariant equivalence preservation:

```agda
  _≡⟨_⟩_ : ∀ x {y z} → x ≡ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≡⟨ refl ⟩ x∼z = x∼z
```

contravariant equivalence preservation:

```agda
  _≡˘⟨_⟩_ : ∀ x {y z} → y ≡ x → y IsRelatedTo z → x IsRelatedTo z
  _ ≡˘⟨ refl ⟩ x∼z = x∼z
```

preservation of reflexivity:

```agda
  _≡⟨⟩_ : ∀ x {y} → x IsRelatedTo y → x IsRelatedTo y
  _ ≡⟨⟩ x∼y = _ ≡⟨ refl ⟩ x∼y
```

and we end chains of reasoning with a QED:

```agda
  _∎ : ∀ x → x IsRelatedTo x
  _∎ _ = relTo reflexive
```

## Some Proofs using equational reasoning

A lot of assymetric laws can be derived with one half of the symmetry and mixing it with commutativity. E.g. left inverse coiuld be derived using right inverse and commutativity, similarly, right inverse can be derived using left inverse and commutativity.


```agda
open import Algebra.operations

module withCommutativity {a ℓ}
  {A : Set a}
  {_∼_ : Rel A ℓ}
  {_•_ : (★ _∼_) A}
  {_⁻¹ : (♠ _∼_) A}
  (reflexive : Reflexive _∼_)
  (trans : Transitive _∼_)
  (comm : Commutative _∼_ _•_)
  (ϵ : A)
  where

    open ★-reasoning _∼_ reflexive trans public
```

```agda
    comm+invˡ⇒invʳ :
        LeftInverse _∼_ ϵ _⁻¹ _•_
      → RightInverse _∼_ ϵ _⁻¹ _•_
    comm+invˡ⇒invʳ invˡ x = begin
      x • (x ⁻¹) ∼⟨ comm x (x ⁻¹) ⟩
      (x ⁻¹) • x ∼⟨ invˡ x ⟩
      ϵ          ∎
```

```agda
    comm+invʳ⇒invˡ : RightInverse _∼_ ϵ _⁻¹ _•_ → LeftInverse _∼_ ϵ _⁻¹ _•_
    comm+invʳ⇒invˡ invʳ x = begin
      (x ⁻¹) • x ∼⟨ comm (x ⁻¹) x ⟩
      x • (x ⁻¹) ∼⟨ invʳ x ⟩
      ϵ          ∎
```

```agda
module withCongruence {a ℓ}
  {A : Set a}
  (_∼_ : Rel A ℓ)
  (_•_ : (★ _∼_) A)
  (_⁻¹ : (♠ _∼_) A)
  (reflexive : Reflexive _∼_)
  (trans : Transitive _∼_)
  (sym : Symmetric _∼_)
  (cong : Congruent₂ _∼_ _•_)
  (ϵ : A)
  where

    open ★-reasoning _∼_ reflexive trans public
```

```agda
    assoc+id+invʳ⇒invˡ-unique :
        Associative _∼_ _•_
      → Identity _∼_ ϵ _•_
      → RightInverse _∼_ ϵ _⁻¹ _•_
      → ∀ x y
      → (x • y) ∼ ϵ
      → x ∼ (y ⁻¹)
    assoc+id+invʳ⇒invˡ-unique assoc (idˡ , idʳ) invʳ x y eq = begin
      x                ∼⟨ sym (idʳ x) ⟩
      x • ϵ            ∼⟨ cong reflexive (sym (invʳ y)) ⟩
      x • (y • (y ⁻¹)) ∼⟨ sym (assoc x y (y ⁻¹)) ⟩
      (x • y) • (y ⁻¹) ∼⟨ cong eq reflexive ⟩
      ϵ • (y ⁻¹)       ∼⟨ idˡ (y ⁻¹) ⟩
      y ⁻¹             ∎
```

```agda
    assoc+id+invˡ⇒invʳ-unique :
        Associative _∼_ _•_
      → Identity _∼_ ϵ _•_
      → LeftInverse _∼_ ϵ _⁻¹ _•_
      → ∀ x y
      → (x • y) ∼ ϵ
      → y ∼ (x ⁻¹)
    assoc+id+invˡ⇒invʳ-unique assoc (idˡ , idʳ) invˡ x y eq = begin
      y                ∼⟨ sym (idˡ y) ⟩
      ϵ • y            ∼⟨ cong (sym (invˡ x)) reflexive ⟩
      ((x ⁻¹) • x) • y ∼⟨ assoc (x ⁻¹) x y ⟩
      (x ⁻¹) • (x • y) ∼⟨ cong reflexive eq ⟩
      (x ⁻¹) • ϵ       ∼⟨ idʳ (x ⁻¹) ⟩
      x ⁻¹             ∎
```
