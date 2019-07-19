<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Gödel's T](#g%C3%B6dels-t)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

****
[Contents](contents.html)

# Gödel's T

```agda
open import Types.equality

module AppliedTypes.godels_t where
```

"Gödel's T", also known as "System T", named after the mathematician [Kurt Gödel](https://en.wikipedia.org/wiki/Kurt_G%C3%B6del), is a system designed by Gödel to provide a consistency proof of arithmetic.

System T basically consists of natural numbers:

```agda
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
```

binary operations on natural numbers:

```agda
-- ⫼_ : ℕ → ℕ → ℕ
-- ⫼ A = A → A → A
```

and functional application:

```snagda
_$_ : {A : ℕ} {B : A → ℕ}
        → ((x : A) → B x)
        → ((x : A) → B x)
f $ x = f x
```

Apart from the ability to only deal with functions on natural numbers, we also need recursion, lambda abstraction, all of which are part of agda itself.

```aesdknagda
succ-nat : ∀ x → x → (succ x)
succ-nat x = (succ x)
```


****
[System F](./AppliedTypes.system_f.html)
