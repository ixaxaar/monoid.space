****
[Contents](contents.html)
[Previous](Types.relations.html)
[Next](Types.operations.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Equalities](#equalities)
- [Definitional Equality](#definitional-equality)
- [Computational Equality](#computational-equality)
- [Propositional Equality](#propositional-equality)
    - [Symmetry](#symmetry)
    - [Transitivity](#transitivity)
    - [Congruence: functions that preserve equality](#congruence-functions-that-preserve-equality)
    - [Substitution](#substitution)
- [Equivalence, with universe polymorphism](#equivalence-with-universe-polymorphism)
    - [Equality](#equality)
    - [Properties of equality](#properties-of-equality)
- [Setoids](#setoids)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Equalities

```agda
module Types.equality where

open import Lang.dataStructures using (
  Bool; true; false;
  ⟂; ⊤; ℕ; List;
  one; two; three; four; five; six; seven; eight; nine; ten; zero; succ; _+_;
  _::_; [])
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Types.functions using (_on_; flip)
open import Types.relations
```

Equality is perhaps one of the most richest but most naively understood concepts. Here we try to provide some structural analysis as to what equality really means in various contexts of mathematics. Equality is treated as a relation in type theory and can be classified broadly as of three kinds:

- Propositional equality
- Computational equality
- Definitional equality

# Definitional Equality

Definitional equality is the most basic notion of equality which appeals to our notion of equality being the sameness of meaning (by definition). For example, `9` and `3 + 3` represent the same thing and hence are definitionally equal `9 ≡ 3²`. Similarly `two ≡ succ (succ zero)`.

```agda
defEqual₁ : ℕ
defEqual₁ = seven

defEqual₂ : ℕ
defEqual₂ = succ (succ five)
```

Here, `defEqual₁` and `defEqual₂` both are equal, with equality of the kind "definitional equality".

# Computational Equality

This kind of equality describes the sameness of types that are not directly equal but can be reduced to be equal. "Reduction" here implies mathematical reduction, referring to rewriting expressions into simpler forms. An example of such an equality is applying a function $$(λ x.x+x)(2) ≡ 2 + 2$$ Expansions of recursors also falls under this kind of equality: $$2 + 2 ≡ succ (succ zero) + succ (succ zero) ≡ succ (succ (succ (succ zero)))$$ Practically, computational equality is included into definitional equality and is also known as "Judgemental equality".

# Propositional Equality

Definitional and computational equalities describe something intrinsic - a property that does not depend upon a proof. For example, `a + b ≡ b + a` cannot be proven to be definitionally equal unless the concrete values of `a` and `b` are known. However, if they're natural numbers `a, b ∈ ℕ`, then the statement `a + b ≡ b + a` requires a proof to claim its truthfulness. Given `a, b ∈ ℕ`, we can prove that `a + b ≡ b + a` or in other words that there exists an identity of type `Id : a + b ≡ b + a` where `Id` is a proposition − exhibiting a term belonging to such a type is exhibiting (i.e. proving) such a propositional equality.

 However, other notions of equalities can be defined that do require proofs. Consider for example natural language - when we say "all flowers are beautiful" the "all flowers" part of the sentence implies all flowers are equal in some way. Or, consider natural numbers `a + b = b + a ∀ a, b ∈ ℕ`. Here we would need to prove the symmetry of the `+` operator in order to prove the equality. Such equalities that require to be specified come under the umbrella of propositional equality. Propositional equality is a kind of equality which requires a proof, and hence the equality itself is also a type `∼`:

```haskell
infix 4 _∼_

data _∼_ {A : Set}(a : A) : {B : Set} → B → Set where
  same : a ∼ a
```

Reflexivity is defined with the definition of `∼` by the keyword `same`, the others being:

### Symmetry

Symmetry is the property where binary a relation's behavior does not depend upon its argument's position (left or right):

```haskell
symmetry : ∀ {A B}{a : A}{b : B}
  → a ∼ b
  → b ∼ a
symmetry same = same
```

### Transitivity

Transitivity is when a binary relation `_∼_` and $x ∼ y and y ∼ z ⟹ x ∼ z$

```haskell
transitivity : ∀ {A B C}{a : A}{b : B}{c : C}
  → a ∼ b
  → b ∼ c
  → a ∼ c
transitivity same p = p
```

### Congruence: functions that preserve equality

Functions that when applied to objects of a type, do not alter the operation of equality can be defined as:

```haskell
congruence : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ∼ y
  → f x ∼ f y
congruence f same = same
```

### Substitution

If `a = b` and if `predicate a = true` ⟹ `predicate b = true`

```haskell
substitution : ∀ {A : Set} {x y : A} (Predicate : A → Set)
  → x ∼ y
  → Predicate x
  → Predicate y
substitution Predicate same p = p
```

Any relation which satisfies the above properties of `reflexivity`, `transitivity` and `symmetry` can be considered an equivalence relation and hence can judge a propositional equality.

# Equivalence, with universe polymorphism

We now present a more formal machinery for relations. We use [universe polymorphism](Types.universe.html#universe-polymorphism) throughout to develop this machinery.

### Equality

We first re-define propositional equality within the framework of universe polymorphism:

```agda
infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x
```

And an equivalence relation for binary relations:

```agda
record IsEquivalence {a ℓ} {A : Set a}
                     (_≈_ : Rel A ℓ) : Set (a ⊔ ℓ) where
  field
    rfl   : Reflexive _≈_
    sym   : Symmetric _≈_
    trans : Transitive _≈_

  reflexive : _≡_ ⇒ _≈_
  reflexive refl = rfl
```

### Properties of equality

We use the new structures to re-define the properties of propositional equality.

```agda
module ≡-properties {a} {A : Set a} where
  sym-≡ : Symmetric {A = A} _≡_
  sym-≡ refl = refl

  trans-≡ : Transitive {A = A} _≡_
  trans-≡ refl p = p

  isEquivalence : IsEquivalence {A = A} _≡_
  isEquivalence = record
    { rfl  = refl
    ; sym   = sym-≡
    ; trans = trans-≡
    }

cong-≡ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y : A}
  → x ≡ y
  → f x ≡ f y
cong-≡ f refl = refl

subs-≡ : ∀ {a} {A : Set a}{x y : A} (Predicate : A → Set)
  → x ≡ y
  → Predicate x
  → Predicate y
subs-≡ Predicate refl p = p
```

# Setoids

Equality, or specifically, equivalence is at the heart of mathematics. In order to build more complex structures, we introduce a new datatype, which essentially encapsulates any datatype and it's equivalence operation:

```agda
record Setoid c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Data          : Set c
    _≈_           : Rel Data ℓ
    isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public
```

****
[Product Types / Σ-types](./Types.product.html)
