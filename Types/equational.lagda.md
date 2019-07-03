<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Equational Reasoning](#equational-reasoning)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

****
[Contents](contents.html)

# Equational Reasoning

```agda
module Types.equational where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Types.equality renaming (cong-≡ to cong)
open import Types.product using (Σ; _,_; _×_)
```

Though we looked at the type theory way of constructively proving propositions, there is another way which we tend to be more familiar with: the way we solve equations on paper. However, note that in practice, "type-hackers", tend to use a combination of both constructive and equational as per convenience as well see below.

For example, consider the problem of proving a well known identity from linear algebra:

```math
∀ a, b ∈ ℕ: (a+b) × (a-b) ≡ a² - b²

(a + b) × (a - b)
    Applying distributivity of + and × (a + b) * c ≡ (a × c) + (b × c)
 = a × (a - b) + b × (a - b)
    Applying distributivity again, this time from the left-hand side
 = a × a - a × b + b × a - b²
    Applying
        1. The fact that a × a ≡ a²
        2. Commutativity of multiplication: a × b ≡ b × a
        3. Reflexivity of ≡ for a × b and b × a to cancel each other out
= a² - b²
Q.E.D.
```

Each step of such a solution essentially follows through the rule of transitivity of equality. Hence setp₂ = step₁ + actions₁ and so on. We can write an apparatus to let us do exactly that in Agda. That apparatus is "equational reasoning". Here, we define the framework on top of equivalence relations:

```sdkefagda
module ≡-Reasoning {a} {A : Set a} where
  open ≡-properties {A = A}
  open IsEquivalence isEquivalence public
```

```agda
module ≡-Reasoning {a} {A : Set a} where
  open ≡-properties {A = A}
  open IsEquivalence isEquivalence public

  infix  3 _∎
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  1 begin_

  -- This is just syntactical sugar to define the start of the proof
  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin_ x≡y = x≡y

  -- Apply reflexivity, no axioms or theorems applied within the ⟨⟩
  _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  -- Transitivity with axioms and theorems applied within the ⟨⟩
  _≡⟨_⟩_ : ∀ (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  -- The QED or "hence, proved" marker to end the proof.
  _∎ : ∀ (x : A) → x ≡ x
  _∎ _ = rfl
```

In order to define $(a+b) × (a-b) ≡ a² - b²$ in Agda, we have to define some properties of `+`, `-` and `*`:

- Distributivity of `+` over `×` from the right side
- Distributivity of `+` over `×` from the left side
- Commutativity of `×`
- Reflexivity of `≡`

We dont need to prove the reflexivity of `≡` as it is a part of our equational reasoning framework as has been already assumed.

```agda
module Properties {a} {A : Set a} where
  open ≡-Reasoning

  -- open ≡-Reasoning eq
  -- open IsEquivalence eq

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  infixl 6 _+_ _−_
  infixl 7 _*_

  _+_ : ℕ → ℕ →  ℕ
  m + zero   = m
  m + succ n = succ (m + n)

  _−_ : ℕ → ℕ → ℕ
  zero  − m     = zero
  succ n − zero  = succ n
  succ n − succ m = n − m

  _*_ : ℕ → ℕ → ℕ
  zero * x     = zero
  (succ x) * y = y + (x * y)

  -- _^_ : ℕ → ℕ → ℕ
  -- x ^ zero = {!!}
  -- x ^ (succ y) = x × (x ^ y)

  +-succ-l : ∀ x y → x + (succ y) ≡ succ (x + y)
  +-succ-l zero    n = refl
  +-succ-l (succ m) n = refl

  +-succ-r : ∀ x y → (succ x) + y ≡ succ (x + y)
  +-succ-r n zero = refl
  +-succ-r m (succ n) = cong succ (+-succ-r m n)

  +-unsucc-l : ∀ x y → succ (x + y) ≡ x + (succ y)
  +-unsucc-l n zero     = refl
  +-unsucc-l n (succ m) = refl

  +-unsucc-r : ∀ x y → succ (x + y) ≡ (succ x) + y
  +-unsucc-r m zero = refl
  +-unsucc-r m (succ n) = cong succ (+-unsucc-r m n)

  +-assoc-l : ∀ x y z → ((x + y) + z) ≡ (x + (y + z))
  +-assoc-l l m zero = refl
  +-assoc-l l m (succ n) = cong succ (+-assoc-l l m n)

  +-assoc-r : ∀ x y z → (x + (y + z)) ≡ ((x + y) + z)
  +-assoc-r l m zero = refl
  +-assoc-r l m (succ n) = cong succ (+-assoc-r l m n)

  +-identity-l : ∀ x → x + zero ≡ x
  +-identity-l _ = refl

  +-identity-r : ∀ x → zero + x ≡ x
  +-identity-r zero    = refl
  +-identity-r (succ n) = cong succ (+-identity-r n)

  +-identity : ∀ x → (x + zero ≡ x) × (zero + x ≡ x)
  +-identity n = (+-identity-l n) , (+-identity-r n)

  +-comm : ∀ x y → (x + y) ≡ (y + x)
  +-comm zero n = +-identity-r n
  +-comm (succ m) n = begin
    (succ m) + n   ≡⟨ +-succ-r m n ⟩
    succ (m + n) ≡⟨ cong succ (+-comm m n) ⟩
    succ (n + m) ≡⟨ refl ⟩
    n + succ m   ∎

  *-succ-l : ∀ x y → succ x * y ≡ y + (x * y)
  *-succ-l m zero = refl
  *-succ-l m (succ n) = refl

  *-succ-r : ∀ x y → x * succ y ≡ x + (x * y)
  *-succ-r zero m = refl
  *-succ-r (succ m) n = begin
    succ m * succ n             ≡⟨⟩
    succ n + m * succ n         ≡⟨ cong (_+_ (succ n)) (*-succ-r m n) ⟩
    succ n + (m + m * n)        ≡⟨ +-succ-r n (m + (m * n)) ⟩
    succ (n + (m + m * n))      ≡⟨⟩
    succ (n + (m + (m * n)))    ≡⟨ cong succ (+-assoc-r n m (m * n)) ⟩
    succ (n + m + m * n)        ≡⟨ cong (λ x → succ (x + m * n)) (+-comm n m) ⟩
    succ ((m + n) + m * n)      ≡⟨ cong succ (+-assoc-l m n (m * n)) ⟩
    succ (m + (n + m * n))      ≡⟨ +-unsucc-r m (n + m * n) ⟩
    (succ m) + (n + m * n)      ≡⟨⟩
    succ m + succ m * n         ∎

  *-zero-r : ∀ x → x * zero ≡ zero
  *-zero-r zero = refl
  *-zero-r (succ n) = begin
    (succ n) * zero ≡⟨ refl ⟩
    zero + n * zero ≡⟨ +-identity-r (n * zero) ⟩
    n * zero ≡⟨ *-zero-r n ⟩
    zero ∎

  *-zero-l : ∀ x → zero * x ≡ zero
  *-zero-l zero = refl
  *-zero-l (succ n) = refl

  *-comm : ∀ x y → x * y ≡ y * x
  *-comm m zero = *-zero-r m
  *-comm m (succ n) = begin
    m * (succ n)  ≡⟨ *-succ-r m n ⟩
    m + m * n ≡⟨ cong (m +_) (*-comm m n) ⟩
    m + n * m ≡⟨ sym (*-succ-l n m) ⟩
    (succ n) * m _∎
```

****
[Logic Introduction](./Logic.introduction.html)
