****
[Contents](contents.html)
[Previous](AppliedTypes.introduction.html)
[Next](AppliedTypes.system_f.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Gödel's T](#g%C3%B6dels-t)
  - [Binary operations](#binary-operations)
  - [Prime numbers](#prime-numbers)
  - [Definability](#definability)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Gödel's T

```agda
open import Types.relations renaming (¬_ to ¬-eq_)
open import Types.equality
open import Level using (0ℓ)
open import Types.product using (_∪_)

module AppliedTypes.godels_t where
```

"Gödel's T", also known as "System T", named after the mathematician [Kurt Gödel](https://en.wikipedia.org/wiki/Kurt_G%C3%B6del), is a formal system designed by Gödel to provide a consistency proof of arithmetic. This system includes a type system based on booleans and natural numbers and allows primitive recursion.

System T basically consists of natural numbers:

```agda
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
```

booleans:

```agda
data Bool : Set where
  true  : Bool
  false : Bool
```

if-then-else:

```agda
if_then_else_ : {C : Set} → Bool → C → C → C
if true  then x else y = x
if false then x else y = y
```

and recursion on natural numbers:

```agda
recₙ : {x : Set} → x → (ℕ → x → x) → ℕ → x
recₙ p h  zero    = p
recₙ p h (succ n) = h n (recₙ p h n)
```

## Binary operations

Addition and multiplication on natural numbers can be defined via recursion:

```agda
_+_ : ℕ → ℕ → ℕ
_+_ n m = recₙ m (λ x y → succ y) n

_*_ : ℕ → ℕ → ℕ
_*_ n m = recₙ zero (λ x y → y + m) n

-- opposite direction of succ
prev : ℕ → ℕ
prev n = recₙ n (λ x y → x) n

_−_ : ℕ → ℕ → ℕ
_−_ n m = recₙ n (λ x y → (prev y)) m

data _≤_ : Rel ℕ 0ℓ where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → succ m ≤ succ n

_<_ : Rel ℕ 0ℓ
m < n = succ m ≤ n

_>_ : Rel ℕ 0ℓ
m > n = n < m
```

Boolean operators can be built on top of if-then-else:

```agda
¬ : Bool → Bool
¬ b = if b then false else true

_∧_ : Bool → Bool → Bool
a ∧ b = if a then b else false

_∨_ : Bool → Bool → Bool
a ∨ b = if a then true else b

_⊕_ : Bool → Bool → Bool
a ⊕ b = if a then (¬ b) else b
```

## Prime numbers

A prime number is defined as a natural number with only two divisors - `1` and itself.

```agda
-- divisibility
infix 4 _∣_ _∤_

record _∣_ (m n : ℕ) : Set where
  constructor divides
  field
    quotient : ℕ
    equality : n ≡ quotient * m
open _∣_ using (quotient) public

_∤_ : Rel ℕ 0ℓ
m ∤ n = ¬-eq (m ∣ n)
```

Prime number definition:

```agda
record Prime (p : ℕ) : Set where
  constructor prime
  field
    -- primes > 2
    p>1 : p > (succ zero)
    -- only 2 divisors - 1 and p
    isPrime  : ∀ {d} → d ∣ p → (d ≡ (succ zero)) ∪ (d ≡ p)
```


## Definability

A function $ f : ℕ → ℕ $ is definable if one can find an expression `e` of `f` such that:

```math
∀ x ∈ ℕ, f(x) ≡ e(x)
```

or in other words, if one can implement the function in system T using only if-then-else and primitive recursion.

If we were to assign a natural number to each such implementation of every function possible, we can treat each expression as data:

```sakdeagda
count = zero
one = succ zero

assign : (ℕ → ℕ) → ℕ
assign f = count + one
```


****
[System F](./AppliedTypes.real.html)
