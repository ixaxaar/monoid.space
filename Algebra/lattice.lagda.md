## Lattice

```lauda
open import Types.equality
open import Algebra.operations

record IsLattice {a ℓ} {A : Set a} {_==_ : Rel A ℓ} (∨ ∧ : ★ A) : Set (a ⊔ ℓ) where
  field
    isEquivalence : IsEquivalence _==_
    ∨-comm        : Commutative ∨
    ∨-assoc       : Associative ∨
    ∨-cong        : Congruent₂ ∨
    ∧-comm        : Commutative ∧
    ∧-assoc       : Associative ∧
    ∧-cong        : Congruent₂ ∧
    absorptive    : Absorptive ∨ ∧

  open IsEquivalence isEquivalence public

  ∨-absorbs-∧ : ∨ Absorbs ∧
  ∨-absorbs-∧ = fst absorptive

  ∧-absorbs-∨ : ∧ Absorbs ∨
  ∧-absorbs-∨ = snd absorptive

  ∧-congˡ : LeftCongruent ∧
  ∧-congˡ y==z = ∧-cong y==z refl

  ∧-congʳ : RightCongruent ∧
  ∧-congʳ y==z = ∧-cong refl y==z

  ∨-congˡ  : LeftCongruent ∨
  ∨-congˡ y==z = ∨-cong y==z refl

  ∨-congʳ : RightCongruent ∨
  ∨-congʳ y==z = ∨-cong refl y==z
```
