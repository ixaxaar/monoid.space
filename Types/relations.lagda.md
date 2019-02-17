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

We begin by constructing relations as types. A relation `∙` between two objects `a` and `b` is a function type:

```agda
Rel : Set → Set1
Rel A = A → A → Set
```

A reflexive relation is one where $ x \bullet y = y \bullet x $ :

```agda
Reflexive : {A : Set}
  → Rel A
  → Set
Reflexive {A} _R_ = (x : A) → x R x
```

A symmetric relation is one where $ x \bullet y \implies y \bullet x $ :

```agda
Symmetric : {A : Set} → Rel A → Set
Symmetric {A} _R_  = (x y : A)
  → x R y
  → y R x
```

A transitive relation is one where $ x \bullet y, y \bullet z then z \bullet x $ :

```agda
Transitive : {A : Set} → Rel A → Set
Transitive {A} _R_ = (x y z : A)
  → x R y
  → y R z
  → x R z
```

A congruent relation is one where a function $ x \bullet y \implies f(x) \bullet f(y) $ or the function `f` preserves the relation :

```agda
Congruent : {A : Set} → Rel A → Set
Congruent {A} _R_ = (f : A → A)(x y : A)
  → x R y
  → f x R f y
```
A substitutive relation is one where $ x \bullet y ~and~ (predicate y) = ⊤ \implies (predicate x) = ⊤ $ :

```agda
Substitutive : {A : Set} → Rel A → Set1
Substitutive {A} _R_ = (P : A → Set)(x y : A)
  → x R y
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
    refl  : Reflexive _==_
    sym   : Symmetric _==_
    trans : Transitive _==_
```

****
[Back to Contents](./contents.html)
