<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Dependent Function Types or Π-types](#dependent-function-types-or-%CF%80-types)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Dependent Function Types or Π-types

```agda
module Types.functions where

open import Lang.dataStructures using (
  Bool; true; false;
  ℕ; List;
  one; two; three; four; five; six; seven; eight; nine; ten; zero; succ;
  _::_; [])
```

Dependent function types or Π-types are functions whose second argument depends upon the first.

i.e. function `f : A → (g A) → Set` where `g : A → B`.

In the notation of lambda abstraction:

$$$
λx. (λx.y).ϕ
$$$

To show how to use this type, we construct an example:

```agda
-- divide by 2
divBy2 : ℕ → ℕ
divBy2 zero = zero
divBy2 (succ zero) = one -- well...
divBy2 (succ (succ n)) = succ (divBy2 n) -- take 2 at a time and count as 1

-- proof of a number being even
even : ℕ → Set
even zero = ⊤
even (succ zero) = ⊥
even (succ (succ n)) = even n
```

Now, we can define a function that divides only even numbers by 2:

```agda
divBy2₂ : (n : ℕ) → even n → ℕ
divBy2₂ zero p = zero
divBy2₂ (succ zero) ()
divBy2₂ (succ (succ y)) p = succ (divBy2₂ y p)
```

In order to be applied, `divBy2₂` requries its input `n` to conform to the type `even n`, which can only exist if the number `n` is even! This makes `divBy2₂` a dependent function.

****
[Back to Contents](./contents.html)
