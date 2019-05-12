<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Relations](#relations)
- [Equivalence relation](#equivalence-relation)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Relations

```agda
module Types.relations where
```

We begin by constructing relations as types. A binary relation `∙` between two objects `a` and `b` is a function type:

```agda
Rel : Set → Set1
Rel A = A → A → Set
```

A relation with universe polymorphism could also be defined as:

```agda
open import Agda.Primitive using (Level; _⊔_; lsuc)

-- heterogenous relation
REL : ∀ {a b} → Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ lsuc ℓ)
REL A B ℓ = A → B → Set ℓ

-- homogenous relation
R : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
R A ℓ = REL A A ℓ
```

The first definition being easier for our purposes here, we proceed that.

A reflexive relation is one where $ x \bullet y = y \bullet x $ :

![refl](refl.png)

```agda
reflexive : {A : Set}
  → Rel A
  → Set
reflexive {A} _★_ = (x : A) → x ★ x
```

A symmetric relation is one where $ x \bullet y \implies y \bullet x $ :

![symmetric](symmetric.png)

```agda
symmetric : {A : Set} → Rel A → Set
symmetric {A} _★_  = (x y : A)
  → x ★ y
  → y ★ x
```

A transitive relation is one where $ x \bullet y, y \bullet z then z \bullet x $ :

![transitive](transitive.png)

```agda
transitive : {A : Set} → Rel A → Set
transitive {A} _★_ = (x y z : A)
  → x ★ y
  → y ★ z
  → x ★ z
```

A congruent relation is one where a function $ x \bullet y \implies f(x) \bullet f(y) $ or the function `f` preserves the relation :

```agda
congruent : {A : Set} → Rel A → Set
congruent {A} _★_ = (f : A → A)(x y : A)
  → x ★ y
  → f x ★ f y
```
A substitutive relation is one where $ x \bullet y ~and~ (predicate y) = ⊤ \implies (predicate x) = ⊤ $ :

```agda
substitutive : {A : Set} → Rel A → Set1
substitutive {A} _★_ = (P : A → Set)(x y : A)
  → x ★ y
  → P x
  → P y
```

# Equivalence relation

An equivalence relation is a relation which is
- reflexive $ a = a $
- symmetric $ if a = b ~then~ b = a $
- transitive $ if a = b ~and~ b = c ~then~ a = c $

All forms of what we know as "equality" are equivalence relations. They help in identifying similar objects and can be "weak" or "strong" depending upon how much similarity they capture of the objects they compare. For e.g. all "tables" fall under one equivalence class wherein when we refer to a generic "table" we mean as in all tables as equal. Whereas, if we were comparing tables amongst themselves, we'd use other finer criteria in our equivalence relations, classifying some tables as coffee tables and so on.

```agda
record Equivalence (A : Set) : Set1 where
  field
    _==_  : Rel A
    refl  : reflexive _==_
    sym   : symmetric _==_
    trans : transitive _==_
```


****
[Back to Contents](./contents.html)
