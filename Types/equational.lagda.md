

# Equational Reasoning

We now look at constructing a language or algebra atop a given relation and some of its properties. This serves as a nicer way of proving things by application of relations such as chains of transitivity.

```agda
{-# OPTIONS --without-K --safe #-}

module Types.equational where

open import Level using (suc; _⊔_)
open import Types.equality as Eq using (Rel; Reflexive; Transitive; _≡_; IsEquivalence)
```

## Trivial example

An equational reasoning framework built upon an equivalence relation:

```agda
module ≡-Reasoning {a ℓ} {A : Set a} {_≡_ : Rel A ℓ} (Eq : IsEquivalence _≡_) where
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
```

We now define a more complex version where there is symmetry in equivalence preservation, unlike the previous naive version where it is only covariant.

## Equational Reasoning over equivalence relations

```agda
module _ {a ℓ} {A : Set a} {_∼_ : Rel A ℓ} (refl : Reflexive _∼_) (trans : Transitive _∼_) where

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
  _ ≡⟨ Eq.refl ⟩ x∼z = x∼z
```

contravariant equivalence preservation:

```agda
  _≡˘⟨_⟩_ : ∀ x {y z} → y ≡ x → y IsRelatedTo z → x IsRelatedTo z
  _ ≡˘⟨ Eq.refl ⟩ x∼z = x∼z
```

preservation of reflexivity:

```agda
  _≡⟨⟩_ : ∀ x {y} → x IsRelatedTo y → x IsRelatedTo y
  _ ≡⟨⟩ x∼y = _ ≡⟨ Eq.refl ⟩ x∼y
```

and we end chains of reasoning with a QED:

```agda
  _∎ : ∀ x → x IsRelatedTo x
  _∎ _ = relTo refl
```
