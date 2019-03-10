<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Equality](#equality)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Equality

```agda
module Logic.equality where

open import Types.relations using (Rel; Equivalence)

open import Logic.logicBasics using (¬; not; xor; ⟂; ⊤; singleton)

open import Lang.dataStructures using (Bool; true; false)
```

Equality, or an equivalence, is the most basic comparison that can be performed between two objects. Let us first see how equality (and inequality) looks like for logical objects:

![equailty](equailty.png)

```agda
data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)
```

Equality can also be derived as a negation of XOR:

$$
a \equiv b ~is~ ~True~ \implies ¬ (a \bigoplus b) ~is~ True
$$

```agda
equal? : Bool → Bool → Bool
equal? a b = not (xor a b)
```

TODO: write the type version as well.

The laws of equality are same as what we saw earlier in [equality](Types.equality.html):

Note, the only difference here is that each law applies to the same datatype, be it `⟂`, `⊤` or `Bool`.

```agda
symmetric : {A : Set} {x y : A}
        → x ≡ y
        → y ≡ x
symmetric {A} refl = refl
```

```agda
transitive : {A : Set} {x y z : A}
        → x ≡ y
        → y ≡ z
        → x ≡ z
transitive {A} refl a = a
```

Let us fit the above proofs of the properties of the relation `≡` to prove an equivalence relation:

```agda
Equiv : {A : Set} → Equivalence A
Equiv = record
  {
    _==_  = _≡_
    ; refl  = \x      → refl
    ; sym   = \x y    → symmetric
    ; trans = \x y z  → transitive
  }
```

To see that this applies to a `singleton`:

```agda
refl⊤ : singleton ≡ singleton
refl⊤  = Equivalence.refl Equiv singleton

sym⊤ : singleton ≡ singleton → singleton ≡ singleton
sym⊤   = Equivalence.sym Equiv singleton singleton

trans⊤ : singleton ≡ singleton → singleton ≡ singleton → singleton ≡ singleton
trans⊤ = Equivalence.trans Equiv singleton singleton singleton
```

We cannot, however, verify this for `⟂` explicitly as we cannot produce an object that does not exist / does not have a constructor.

Inequality `≢` cannot serve as an equivalence relation as reflexivity and transitivity cannot be satisfied, though symmetry can:

```agda
symmetric≢ : {A : Set} {x y : A}
        → x ≢ y
        → y ≢ x
symmetric≢ np p = np (symmetric p)
```

****
[Back to Contents](./contents.html)

