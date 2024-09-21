****
[Contents](contents.html)
[Previous](Logic.laws.html)
[Next](Algebra.introduction.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Decidability](#decidability)
  - [1. Evidence based](#1-evidence-based)
  - [2. Computation based](#2-computation-based)
- [Going Further](#going-further)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Decidability

```agda
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Lang.dataStructures using (
  Bool; true; false;
  ℕ; List;
  one; two; three; four; five; six; seven; eight; nine; ten; zero; succ;
  _::_; [])

open import Logic.logicBasics using (
  ⟂; ⊤; ⟂-elim; ¬;
  not; contradiction; contrapos;
  _then_else_)

open import Types.relations using (Rel; REL)
open import Types.equality using (_≡_)

module Logic.decidability where
```

Relations can de defined either as an inductive data type − the existence of the type implies that the relation exists. We say that the data type provides a **witness** that the relation is valid. The other way is to define relations as functions that compute whether the relation holds.

Consider the relation `_<=_`. If we have to prove that `2 <= 4`, we can do that in two ways:

## 1. Evidence based

The Inductive relation:

```agda
data _<=_ : ℕ → ℕ → Set where
  ltz : {n : ℕ} → zero <= n
  lt : {m : ℕ} → {n : ℕ} → m <= n → (succ m) <= (succ n)
```

Proof that 2 ≤ 4:

```agda
2≤4 : two <= four
2≤4 = lt (lt ltz)
```

## 2. Computation based

Relation as a Function type:

```agda
infix 4 _≤_

_≤_ : ℕ → ℕ → Bool
zero ≤ n       =  true
succ m ≤ zero   =  false
succ m ≤ succ n  =  m ≤ n
```

Proof that 2 ≤ 4:

```agda
open import Types.equational
open ≡-Reasoning

twoLessThanFour : (two ≤ four) ≡ true
twoLessThanFour = begin
    two ≤ four
  ≡⟨⟩
    one ≤ three
  ≡⟨⟩
    zero ≤ two
  ≡⟨⟩
    true
  ∎
```

We can always connect such forms of representation of the same underlying mathematical structures from the Computation based to evidence  based:

```agda
T : Bool → Set
T true = ⊤
T false = ⟂
```

Like we saw for the proposition `2 ≤ 4`, for any proposition `P` to be decidable, either we can compute `P` or `¬ P`, i.e. either proposition `P` has a proof or it can been disproved. In the words of logic, a true/false decision problem is decidable if there exists an effective method for deriving the correct answer.

For representing this idea we use an inductive data type which has two constructors.

```agda
data Dec {p} (P : Set p) : Set p where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P
```

The computational equivalent of decidable relations would be:

```agda
Decidable : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ → Set _
Decidable _∼_ = ∀ x y → Dec (x ∼ y)
```

Decidability can be computed into a boolean value. We write that and some other useful machinery:

```agda
⌊_⌋ : ∀ {p} {P : Set p} → Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false
```

```agda
True : ∀ {p} {P : Set p} → Dec P → Set
True Q = T ⌊ Q ⌋
```

```agda
False : ∀ {p} {P : Set p} → Dec P → Set
False Q = T (not ⌊ Q ⌋)
```

```agda
record Lift {a} ℓ (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A

module _ {p} {P : Set p} where
  From-yes : Dec P → Set p
  From-yes (yes _) = P
  From-yes (no  _) = Lift p ⊤
```

We can now use this machinery to prove that the relation `<=` is decidable for all `x, y ∈ ℕ`:

```agda
nothingIsLessThanZero : ∀ {x : ℕ} → ¬ (succ x <= zero)
nothingIsLessThanZero ()

successionsAreLessToo : ∀ {x y : ℕ} → ¬ (x <= y) → ¬ (succ x <= succ y)
successionsAreLessToo ¬x≤y (lt x≤y) = ¬x≤y x≤y

_≤isDecidable_ : ∀ (m n : ℕ) → Dec (m <= n)
zero  ≤isDecidable n                   =  yes ltz
succ m ≤isDecidable zero               =  no nothingIsLessThanZero
succ m ≤isDecidable succ n with m ≤isDecidable n
...               | yes m≤n  =  yes (lt m≤n)
...               | no ¬m≤n  =  no (successionsAreLessToo ¬m≤n)
```

We have used the `with` abstraction above. It lets you pattern match on the result of an intermediate computation by effectively adding an extra argument to the left-hand side of your function. Refer to more documentation [here](https://agda.readthedocs.io/en/v2.5.2/language/with-abstraction.html).

# Going Further

A theory is a set of formulas, often assumed to be closed under logical consequence. Decidability for a theory concerns whether there is an effective procedure that decides whether the formula is a member of the theory or not, given an arbitrary formula in the signature of the theory. The problem of decidability arises naturally when a theory is defined as the set of logical consequences of a fixed set of axioms.

Every consistent theory is decidable, as every formula of the theory will be a logical consequence of, and thus a member of, the theory. First-order logic is not decidable in general; in particular, the set of logical validities in any signature that includes equality and at least one other predicate with two or more arguments is not decidable. Logical systems extending first-order logic, such as second-order logic and type theory, are also undecidable.

Decidability and undecidability of an entire theory can be proven, one of the more famous proofs being [Gödel's incompleteness theorems](https://en.wikipedia.org/wiki/G%C3%B6del%27s_incompleteness_theorems). The machinery we defined here form the basis of a larger set of structures required to prove the above facts, including problems like prime number generation. In light of the complexity associated with such a task, we choose to move on instead.

****
[Introduction](./Algebra.introduction.html)
