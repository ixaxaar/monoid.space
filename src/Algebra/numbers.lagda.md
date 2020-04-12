<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Numbers](#numbers)
  - [Natural numbers](#natural-numbers)
  - [Integers](#integers)
  - [Rational numbers](#rational-numbers)
    - [Dedekind cuts](#dedekind-cuts)
    - [Cauchy sequences](#cauchy-sequences)
  - [Real numbers](#real-numbers)
  - [Complex numbers](#complex-numbers)
  - [Rational numbers](#rational-numbers-1)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

****
[Contents](contents.html)
[Previous](Algebra.rings.html)
[Next](./HoTT.introduction.html)

# Numbers

```agda
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Logic.logicBasics using (if_then_else_)
open import Lang.dataStructures using (Bool; true; false)

open import Types.product
open import Types.relations
open import Types.equality

module Algebra.numbers {a ℓ} {A : Set a} (_==_ : Rel A ℓ) where
  open import Types.operations (_==_)

  open import Algebra.order (_==_)
  open import Algebra.groups (_==_)
  open import Algebra.rings (_==_)
  open import Algebra.fields (_==_)
```

In the previous sections we looked at structures, starting from the very simple groups and monoids, which comprise of a type and one binary operation to fields of a type and two binary operations. We now look at how to construct the most known objects in all of mathematics: numbers.

## Natural numbers

Natural numbers are integral numbers greater than 0, e.g. `1, 2, 3, 4, ... ∈ ℕ`. Note that infinity `∞` is not a natural number. They are the easiest to construct among the numbers and as a successive pattern of creation is all the structure that is required:

```agda
  data ℕ : Set where
    0# : ℕ
    succ : ℕ → ℕ

  _+_ : ℕ → ℕ → ℕ
  x + 0# = x
  x + (succ y) = succ (x + y)

  _−_ : ℕ → ℕ → ℕ
  0#  − m     = 0#
  succ n − 0#  = succ n
  succ n − succ m = n − m

  _✖_ : ℕ → ℕ → ℕ
  x ✖ 0#     = 0#
  x ✖ (succ y) = x + (x ✖ y)

  _<_ : ℕ → ℕ → Bool
  0# < succ x = true
  x < 0# = false
  succ x < succ y = x < y
```

Note that we cannot define division operation on natural numbers as the output may not be a natural number.

## Integers

Integers can either be positive or negative natural numbers.

```agda
  data ℤ : Set where
    pos : (n : ℕ) → ℤ
    neg : (n : ℕ) → ℤ

  _⊕_ : ℤ → ℤ → ℤ
  pos x ⊕ pos y = pos (x + y)
  pos x ⊕ neg y = if (x < y) then neg (y − x) else pos (x − y)
  neg x ⊕ pos y = if (y < x) then neg (x − y) else pos (y − x)
  neg x ⊕ neg y = neg (x + y)

  _⊖_ : ℤ → ℤ → ℤ
  pos x ⊖ pos y = if (y < x) then pos (x − y) else neg (y − x)
  pos x ⊖ neg y = pos (x + y)
  neg x ⊖ pos y = neg (x + y)
  neg x ⊖ neg y = if (x < y) then neg (y − x) else pos (x − y)

  _⊗_ : ℤ → ℤ → ℤ
  pos x ⊗ pos y = pos (x ✖ y)
  pos x ⊗ neg y = neg (x ✖ y)
  neg x ⊗ pos y = neg (x ✖ y)
  neg x ⊗ neg y = pos (x ✖ y)

  _⧀_ : ℤ → ℤ → Bool
  pos x ⧀ pos y = x < y
  pos x ⧀ neg y = false
  neg x ⧀ pos y = true
  neg x ⧀ neg y = y < x
```

## Rational numbers

A rational number is a quotient or fraction of two integers:

```agda
  data ℚ : Set where
    _⨸_ : ℤ → ℤ → ℚ

  numerator : ℚ → ℤ
  numerator (n ⨸ d) = n

  denominator : ℚ → ℤ
  denominator (n ⨸ d) = d

  _⊞_ : ℚ → ℚ → ℚ
  (a ⨸ b) ⊞ (c ⨸ d) = ((a ⊗ d) ⊕ (c ⊗ b)) ⨸ (b ⊗ d)

  _⊟_ : ℚ → ℚ → ℚ
  (a ⨸ b) ⊟ (c ⨸ d) = ((a ⊗ d) ⊖ (c ⊗ b)) ⨸ (b ⊗ d)

  _⧆_ : ℚ → ℚ → ℚ
  (a ⨸ b) ⧆ (c ⨸ d) = (a ⊗ c) ⨸ (b ⊗ d)

  _⧄_ : ℚ → ℚ → ℚ
  (a ⨸ b) ⧄ (c ⨸ d) = (a ⊗ d) ⨸ (b ⊗ c)

  _⪦_ : ℚ → ℚ → Bool
  (a ⨸ b) ⪦ (c ⨸ d) = ((a ⊗ d) ⧀ (c ⊗ b))
```

The rational numbers, when represented using digits (0-9), can either be of finite decimal places, or of infinite decimal places but repetitive (e.g. 4.35353535...). Note that the denominator cannot be zero, as ∞ is not a rational number (it's not considered to be any kind of number). Since rational numbers can be added, multiplied, subtracted and divided using integer operations all resulting in rational numbers, they form a field.

We know all of the above kinds of numbers as represented with a string of digits `0-9` e.g. 3724765.1245. In other words, if we were to take the ten digits and arrange them in a certain order, we would get an integer. Same remains true for rational numbers, though they require two integers. Though this "decimal" representation of numbers are almost unanimously used, they are difficult to work with in mathematics. Hence alternate representations, which tend to be easier, are preferred, though the decimal representations have been shown to follow all the rules of the above definitions.

Real numbers, which include the natural numbers, integers, rational and irrational numbers, are harder to construct as compared to natural numbers. Real numbers, as they include irrational numbers, are numbers with infinite precision. Consider the simplest operation on these numbers: addition: the traditional way of adding two numbers - starting from the right-most decimal, becomes impossible as in case of arbitrary precision numbers there is no right-most digit! Natural numbers, integers and rational numbers are discrete systems and do not face this problem of infinity. We therefore need to define real numbers using another, more manageable representation - as complete ordered fields. The completeness here can imply two different things - Cauchy and Dedekind completeness, either of which when satisfied, satisfies the other and we can then call the objects of the ordered field "real numbers".

### Dedekind cuts



### Cauchy sequences


The constructive definition of a real number is based on the algebraic object "Fields" we saw in the last section. There we first defined fields, followed by fields with ordering, also called "Ordered Fields". We now use the definitions of ordered fields to construct real numbers. As a byproduct, we also show how to construct complex and rational numbers.


## Real numbers

Real numbers and their two operations, + and -, form a field. There are a few additional restrictions imposed on how + and - are to behave with ≤. Real numbers represent:

- A set $ ℝ $
- Two binary operations: + and −

where the structure defined on the operations are:

1. $ ℝ $ is a field under addition and multiplication, which implies:
  - $ ℝ $ is an abelian group under addition, which implies the operation +:
      - is associative
      - is commutative
      - has an inverse (−)
      - has an identity
  - $ ℝ $ is a monoid under multiplication, which implies the operation *:
      - is associative
      - is commutative
      - has an inverse (÷)
      - has an identity
  - Multiplication is distributive over addition
  - There must be an annihilating element 𝕖 such that $ ∀ x : 𝕖 ★ x = 𝕖 $
2. $ ℝ $ forms a totally ordered set over ≤, which implies ≤ is:
  - reflexive
  - antisymmetric
  - transitive
  - total
3. Addition and multiplication are compatible with ≤:
  - addition preserves order `if x ≤ y then x + ε ≤ y + ε`
  - multiplication preserves order `if 0 ≤ x and 0 ≤ y then 0 ≤ x * y`
4. The order ≤ is "complete" or without gaps, also known as "Dedekind completeness", which states that for every subset 𝕣 of ℝ, there exists an 𝕩 ∈ ℝ, such that $ 𝕩 = sup (𝕣) $ or 𝕩 is the least upper bound of 𝕣.

```agda
  record IsRealNumber (_+_ _*_ : ★ A) (-_ ÷_ : ♠ A) (_≤_ : Rel A ℓ) (0# 1# : A) : Set (a ⊔ ℓ) where
    field
      isOrderedField   : IsOrderedField _+_ _*_ -_ ÷_ _≤_ 0# 1#
      +-preservesOrder : ∀ n → (_+ n) Preserves _≤_ ⟶ _≤_
      *-preservesOrder : (_* 0#) Preserves _≤_ ⟶ _≤_

    open IsOrderedField isOrderedField public
```

## Complex numbers

## Rational numbers

****
[HoTT Introduction](./HoTT.introduction.html)
