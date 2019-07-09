****
[Contents](contents.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Equational Reasoning over equivalence relations](#equational-reasoning-over-equivalence-relations)
- [Some Proofs using equational reasoning](#some-proofs-using-equational-reasoning)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

```agda
module Types.equational2 where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Types.equality
open import Types.product using (Σ; _,_)
```

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

****
[Introduction](./Logic.introduction.html)
