****
[Contents](contents.html)
[Previous](Types.equational.html)
[Next](AppliedTypes.introduction.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

  - [Equational Reasoning over equivalence relations](#equational-reasoning-over-equivalence-relations)
  - [Some Proofs using equational reasoning](#some-proofs-using-equational-reasoning)
    - [Commutativity and left inverse yields right inverse](#commutativity-and-left-inverse-yields-right-inverse)
    - [Commutativity and right inverse yields left inverse](#commutativity-and-right-inverse-yields-left-inverse)
    - [Uniqueness of left inverse](#uniqueness-of-left-inverse)
    - [Uniqueness of right inverse](#uniqueness-of-right-inverse)
- [Relations other than equality](#relations-other-than-equality)
- [Equational reasoning for any operator](#equational-reasoning-for-any-operator)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

```agda
module Types.equational2 where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Types.relations
open import Types.equality
open import Types.product using (Σ; _,_)
```

We now define a more complex version of equational reasoning on top of an equivalence relation `_~_` rather than on equality.

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

This seemingly unnecessary type is used to make it possible to infer arguments even if the underlying equality evaluates.

```agda
  data _IsRelatedTo_ (x y : A) : Set (a ⊔ ℓ) where
    relTo : (x∼y : x ∼ y) → x IsRelatedTo y
```

Use this to indicate beginning of reasoning:

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

A lot of asymmetric laws can be derived with one half of the symmetry and mixing it with commutativity. E.g. left inverse could be derived using right inverse and commutativity, similarly, right inverse can be derived using left inverse and commutativity.


```agda
open import Types.operations

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

### Commutativity and left inverse yields right inverse

```agda
    comm+invˡ⇒invʳ :
        LeftInverse _∼_ ϵ _⁻¹ _•_
      → RightInverse _∼_ ϵ _⁻¹ _•_
    comm+invˡ⇒invʳ invˡ x = begin
      x • (x ⁻¹) ∼⟨ comm x (x ⁻¹) ⟩
      (x ⁻¹) • x ∼⟨ invˡ x ⟩
      ϵ          ∎
```

### Commutativity and right inverse yields left inverse

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

### Uniqueness of left inverse

Given an operation is associative, has an identity, every given right inverse has a unique left inverse.

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

### Uniqueness of right inverse

Given an operation is associative, has an identity, every given left inverse has a unique right inverse.

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

# Relations other than equality

Equational reasoning can also be done on other relations except equality and equivalence ones. For example, here we derive the framework for the order operator `_<=_`:

```agda
open import Types.proofsAsData using (_<=_; ltz; lt)
open import Lang.dataStructures
open import Types.relations hiding (Rel)

≤-trans : Transitive {A = ℕ} _<=_
≤-trans ltz j≤k = ltz
≤-trans (lt x) (lt y) = lt (≤-trans x y)

module ≤-Reasoning where
  infix  3 _■
  infixr 2 _≤⧏⧐_ _≤⧏_⧐_
  infix  1 begin_

  begin_ : ∀ {x y : ℕ} → x <= y → x <= y
  begin_ x≤y = x≤y

  -- Apply reflexivity, arguments required within the ⧏⧐
  _≤⧏⧐_ : ∀ (x {y} : ℕ) → x <= y → x <= y
  _ ≤⧏⧐ x≤y = x≤y

  -- Transitivity with arguments applied within the ⧏⧐
  _≤⧏_⧐_ : ∀ (x {y z} : ℕ) → x <= y → y <= z → x <= z
  _ ≤⧏ x≤y ⧐ y≤z = ≤-trans x≤y y≤z

  _■ : ∀ (x : ℕ) → x <= x
  _■ zero = ltz
  _■ (succ x) = lt (_■ x)
```

# Equational reasoning for any operator

As we see the pattern above, given the proof for transitivity of an operator, we can generate the constructs for doing equational with the operator.

```agda
module λ-Reasoning {a ℓ}
  {A : Set a}
  {_⌬_ : Rel A ℓ}
  {⌬-trans : Transitive _⌬_}
  {⌬-refl : Reflexive _⌬_}
  where

  infix  3 _▐
  infixr 2 _⌬◀▶_ _⌬◀_▶_
  infix  1 begin_

  begin_ : ∀ {x y : A} → x ⌬ y → x ⌬ y
  begin_ x⌬y = x⌬y

  -- Apply reflexivity, arguments required within the ◀▶
  _⌬◀▶_ : ∀ (x {y} : A) → x ⌬ y → x ⌬ y
  _ ⌬◀▶ x⌬y = x⌬y

  -- Transitivity with arguments applied within the ◀▶
  _⌬◀_▶_ : ∀ (x {y z} : A) → x ⌬ y → y ⌬ z → x ⌬ z
  _ ⌬◀ x⌬y ▶ y⌬z = ⌬-trans x⌬y y⌬z

  _▐ : ∀ (x : A) → x ⌬ x
  _▐ _ = ⌬-refl
```

****
[Introduction](./Logic.introduction.html)
