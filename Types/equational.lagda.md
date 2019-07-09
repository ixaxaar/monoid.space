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

For example, consider the problem of proving a well known identity for natural numbers from linear algebra:

```math
∀ a, b ∈ ℕ: (a+b)² ≡ a² + 2 * a * b + b²

(a + b) × (a + b)
    Applying distributivity of + and × (a + b) * c ≡ (a × c) + (b × c)
 = a × (a + b) + b × (a + b)
    Applying distributivity again, this time from the left-hand side
 = a × a + a × b + b × a + b²
    Applying
        1. The fact that a × a ≡ a²
        2. Commutativity of multiplication: a × b ≡ b × a
        3. Reflexivity of ≡ for a × b and b × a to add to 2 times
= a² + 2 * a * b + b² 
Q.E.D.
```

Each step of such a solution essentially follows through the rule of transitivity of equality. Hence setp₂ = step₁ + actions₁ and so on. We can write an apparatus to let us do exactly that in Agda. That apparatus is "equational reasoning". Here, we define the framework on top of equivalence relations:

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

Since we are proving this literally from scratch, we have to prove quite a few basic constructions:

```agda
module Properties {a} {A : Set a} where
  open ≡-Reasoning
```

We start with the type of natural numbers:

```agda
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
```

We then proceed to define the required operations on natural numbers:

```agda
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

  _² : ℕ → ℕ
  x ² = x * x
```

We now prove properties of addition, upto commutativity:

```agda
  one = succ zero
  two = succ (succ zero)

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
```

As we saw, we had to prove quite a few laws in their right and left handed versions. These will come in handy later, in fact some of them have been written while trying to prove later propositions. This highlights a central way of solving mathematics - proofs are broken up into pieces and each piece is solved separately. Mostly such smaller proofs tend to be inductively proved and used to prove more complex proofs using equational reasoning.

We now proceed to prove some propositions for multiplication:

```agda
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
    (succ n) * zero       ≡⟨⟩
    zero + n * zero       ≡⟨ +-identity-r (n * zero) ⟩
    n * zero              ≡⟨ *-zero-r n ⟩
    zero                  ∎

  *-zero-l : ∀ x → zero * x ≡ zero
  *-zero-l zero = refl
  *-zero-l (succ n) = refl

  *-identity-l : ∀ x → one * x ≡ x
  *-identity-l zero = refl
  *-identity-l (succ n) = refl

  *-comm : ∀ x y → x * y ≡ y * x
  *-comm m zero = *-zero-r m
  *-comm m (succ n) = begin
    m * (succ n)        ≡⟨ *-succ-r m n ⟩
    m + m * n           ≡⟨ cong (m +_) (*-comm m n) ⟩
    m + n * m           ≡⟨ sym (*-succ-l n m) ⟩
    (succ n) * m        ∎

  *-identity-r : ∀ x → x * one ≡ x
  *-identity-r zero = refl
  *-identity-r (succ n) = begin
    (succ n) * one          ≡⟨⟩
    one + n * one           ≡⟨ cong (_+_ one) (*-identity-r n) ⟩
    (succ zero) + n         ≡⟨ +-succ-r zero n ⟩
    succ (zero + n)         ≡⟨ cong (λ x → succ x) (+-comm zero n) ⟩
    succ (n + zero)         ≡⟨⟩
    succ n                  ∎

  *-succ-r-r : ∀ x y → x * succ y ≡ (x * y) + x
  *-succ-r-r zero m = refl
  *-succ-r-r (succ m) n = begin
    succ m * succ n             ≡⟨ *-succ-r (succ m) n ⟩
    succ m + succ m * n         ≡⟨ +-comm (succ m) (succ m * n) ⟩
    succ m * n + succ m         ∎
```

Here we see a noteworthy pattern, 

To prove for example `a + (b * c) + d ≡ a + (c * b) + d`, we have to apply commutativity only to `(b * c)` only while keeping the rest as it is. This is often achieved by using congruence over lambda pattern matching expressions in agda like `cong (λ x a + x + d) (*-comm b c)`. Or in other words,

```haskell
a + (b * c) + d     ≡⟨ cong (λ x a + x + d) (*-comm b c) ⟩
a + (c * b) + d     ∎
```

Note that the above proofs might not be the best way to prove these propositions.

We now prove the distributive property of `*` over `+`:

```agda
  +-distrib-*-r : ∀ x y z → x * (y + z) ≡ (x * y) + (x * z)
  +-distrib-*-r l m zero = begin
    l * (m + zero)            ≡⟨⟩
    l * m                     ≡⟨⟩
    (l * m) + zero            ≡⟨ cong ((l * m) +_) (sym (*-zero-r l)) ⟩
    (l * m) + (l * zero)      ∎
  +-distrib-*-r l m (succ n) = begin
    l * (m + (succ n))        ≡⟨⟩
    l * succ (m + n)          ≡⟨ *-succ-r l (m + n) ⟩
    l + l * (m + n)           ≡⟨ +-comm l (l * (m + n)) ⟩
    l * (m + n) + l           ≡⟨ cong (λ z → z + l) (+-distrib-*-r l m n) ⟩
    ((l * m) + (l * n)) + l   ≡⟨ +-assoc-l (l * m) (l * n) l ⟩
    (l * m) + ((l * n) + l)   ≡⟨ cong ((l * m) +_) (sym (*-succ-r-r l n)) ⟩
    (l * m) + l * (succ n)    ∎

  +-distrib-*-l : ∀ x y z → (x + y) * z ≡ (x * z) + (y * z)
  +-distrib-*-l zero m n = begin
    (zero + m) * n            ≡⟨ *-comm (zero + m) n ⟩
    n * (zero + m)            ≡⟨ +-distrib-*-r n zero m ⟩
    (n * zero) + (n * m)      ≡⟨ cong (λ x → x + (n * m)) (*-comm n zero) ⟩
    (zero * n) + (n * m)      ≡⟨ cong (λ x → (zero * n) + x) (*-comm n m) ⟩
    (zero * n) + (m * n)      ∎
  +-distrib-*-l (succ l) m n = begin
    ((succ l) + m) * n        ≡⟨ cong (λ x → x * n) (+-succ-r l m) ⟩
    succ (l + m) * n          ≡⟨⟩
    n + ((l + m) * n)         ≡⟨ cong (_+_ n) (+-distrib-*-l l m n) ⟩
    n + (l * n + m * n)       ≡⟨ +-assoc-r n (l * n) (m * n) ⟩
    (n + l * n) + (m * n)     ≡⟨⟩
    (succ l) * n + m * n      ∎
```

And now, finally the proof of our original proposition:

```agda
  proof : ∀ x y → (x + y) ² ≡ (x ² + two * (x * y) + y ²)
  proof zero n = begin
    (zero + n) * (zero + n)
        ≡⟨ cong (λ x → (zero + n) * x) (+-identity-r n) ⟩
    (zero + n) * n
        ≡⟨ cong (λ x → x * n) (+-identity-r n) ⟩
    n * n
        ≡⟨⟩
    n ²
        ≡⟨⟩
    n ² + zero
        ≡⟨ cong ((n ²) +_) (sym (*-zero-r zero)) ⟩
    n ² + (zero * zero)
        ≡⟨⟩
    n ² + zero ²
        ≡⟨ +-comm (n ²) (zero ²) ⟩
    (zero ² + n ²)
        ≡⟨⟩
    (zero ² + n ²) + zero
        ≡⟨ cong ((zero ² + n ²) +_) (sym (*-zero-r (two))) ⟩
    (zero ² + n ²) + (two * zero)
        ≡⟨⟩
    (zero ² + n ²) + (two * zero * n)
        ≡⟨ +-assoc-l (zero ²) (n ²) (two * zero * n) ⟩
    zero ² + (n ² + (two * zero * n))
        ≡⟨ cong (λ x → zero ² + x) (+-comm (n ²) (two * zero * n)) ⟩
    zero ² + ((two * zero * n) + n ²)
        ≡⟨ +-assoc-r (zero ²) (two * zero * n) (n ²) ⟩
    zero ² + two * zero * n + n ²
        ∎
  proof (succ m) n = begin
    ((succ m) + n) * ((succ m) + n)
        ≡⟨ +-distrib-*-l (succ m) n (succ m + n) ⟩
    (succ m) * (succ m + n) + n * (succ m + n)
        ≡⟨ cong (λ x → x + n * (succ m + n)) (+-distrib-*-r (succ m) (succ m) n) ⟩
    (succ m) * (succ m) + (succ m) * n + n * (succ m + n)
        ≡⟨ cong (λ x → (succ m) * (succ m) + (succ m) * n + x) (+-distrib-*-r n (succ m) n) ⟩
    (succ m) * (succ m) + (succ m) * n + (n * (succ m) + n * n)
        ≡⟨ +-assoc-r ((succ m) * (succ m) + (succ m) * n) (n * (succ m)) (n * n)  ⟩
    (succ m) * (succ m) + (succ m) * n + n * (succ m) + n * n
        ≡⟨ cong (λ x → (succ m) * (succ m) + (succ m) * n + x + n * n) (*-comm n (succ m)) ⟩
    (succ m) * (succ m) + (succ m) * n + (succ m) * n + n * n
        ≡⟨⟩
    (succ m) ² + (succ m) * n + (succ m) * n + n * n
        ≡⟨⟩
    ((succ m) ² + (succ m) * n) + (succ m) * n + n ²
        ≡⟨ cong (_+ n ²) (+-assoc-l ((succ m) ²) ((succ m) * n) ((succ m) * n)) ⟩
    (succ m) ² + (succ m * n + succ m * n) + n ²
        ≡⟨ cong (λ x → (succ m) ² + x + n ²) (sym (*-identity-r ((succ m) * n + (succ m) * n))) ⟩
    (succ m) ² + ( (succ m * n) + (succ m * n) ) * one + n ²
        ≡⟨ refl ⟩
    (succ m) ² + ((succ m * n) + (succ m * n)) * one + n ²
        ≡⟨ cong (λ x → (succ m) ² + x + n ²) (+-distrib-*-l (succ m * n) (succ m * n) one) ⟩
    (succ m) ² + ((succ m * n) * one + (succ m * n) * one) + n ²
        ≡⟨ cong (λ x → (succ m) ² + x + n ²) (sym (+-distrib-*-r (succ m * n) one one)) ⟩
    (succ m) ² + ((succ m * n) * (one + one)) + n ²
        ≡⟨⟩
    (succ m) ² + ((succ m * n) * two) + n ²
        ≡⟨ cong (λ x → (succ m) ² + x + n ²) (*-comm (succ m * n) two) ⟩
    (succ m) ² + two * ((succ m) * n) + n ²
        ∎
```

****
[Equational Reasoning 2](./Types.equational2.html)
