
module dogfood.test where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

one   = succ zero
two   = succ one
three = succ two
four  = succ three
five  = succ four
six   = succ five
seven = succ six
eight = succ seven
nine  = succ eight
ten   = succ nine

record Pair (A B : Set) : Set where
  field
    fst : A
    snd : B

p23 : Pair ℕ ℕ
p23 = record { fst = one; snd = three }


x : ℕ
x = Pair.fst p23
