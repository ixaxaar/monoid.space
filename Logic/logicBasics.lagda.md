<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Constructing Logic using type theory](#constructing-logic-using-type-theory)
  - [Objects of Logic](#objects-of-logic)
    - [Empty / False](#empty--false)
    - [Singleton / True](#singleton--true)
  - [Laws or "APIs" of Logic](#laws-or-apis-of-logic)
    - [Elimination](#elimination)
    - [Negation](#negation)
    - [Contradiction](#contradiction)
    - [Contraposition](#contraposition)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Constructing Logic using type theory

Here we look at constructing logic using type theory. Now, mostly all branches of mathematics involve two kinds of entities: objects and propositions about those objects. This very much corresponds to basic composition of programming languages - objects and their APIs.

```agda
module Logic.logicBasics where

open import Level
```

## Objects of Logic

### Empty / False

Type with no object - cannot ever create an object of this type. This makes it possible to define absurd functions, which map `⟂` to anything, as given nothing, one can create anything, or assuming any `False` statement can serve as a proof for anything, which is absurd.

```agda
data ⟂ : Set where
```

Absurd can imply anything, be it true or not. Thus, any statement can be proven using absurdity.

However, it is, we argue, impossible to create an object of absurd type (as `⟂` has no constructor) and hence these functions make no sense in the "real world", as in they can never be invoked. This is called the "absurd pattern".


### Singleton / True

Set with only one object: `True`.

```agda
data ⊤ : Set where
  singleton : ⊤
```

## Laws or "APIs" of Logic

### Elimination

The absurd pattern for proving `Whatever`:

```agda
⟂-elim : ∀ {w} {Whatever : Set w} → ⟂ → Whatever
⟂-elim ()
```

### Negation

We use the fact that a negation of a proposition `P` (to exist and hence be true) implies `¬ P` has to be false, `⟂`.

```agda
¬ : ∀ {a} → Set a → Set a
¬ P = P → ⟂
```

### Contradiction

Either `A → ⟂` is true or `¬ A → ⟂` is true either way, we can `⟂-elim` it:

```agda
contradiction : ∀ {p w} {P : Set p} {Whatever : Set w} → P → ¬ P → Whatever
contradiction p (¬p) = ⟂-elim (¬p p)
```

### Contraposition

We can prove a contraposition with the help of a contradiction:

```agda
contrapos : ∀ {a b} {A : Set a}{B : Set b} → (A → B) → ¬ B → ¬ A
contrapos f ¬b a = contradiction (f a) ¬b
```


****
[Back to Contents](./contents.html)
