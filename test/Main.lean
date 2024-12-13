import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Basic

inductive Boolean : Type
  | false
  | true

-- Example usage
def negation (b : Boolean) : Boolean :=
  match b with
  | Boolean.true => Boolean.false
  | Boolean.false => Boolean.true


inductive Unit' : Type
  | unit

inductive Empty' : Type

theorem negation_involutive : ∀ (b : Boolean), negation (negation b) = b :=
  fun b =>
    match b with
    | Boolean.true =>
      calc
        negation (negation Boolean.true)
        = negation Boolean.false        := rfl
        = Boolean.true                  := rfl
    | Boolean.false =>
      calc
        negation (negation Boolean.false)
        = negation Boolean.true         := rfl
        = Boolean.false                 := rfl

-- #check negation_involutive



-- example (n : Nat) : n + 0 = n := by
--   trace "Starting proof"


Type 0  -- Also written as Type, the universe of "small" types
Type 1  -- The universe containing Type 0
Type 2  -- The universe containing Type 1

#check String

#check List

def liftType.{u} (α : Type u) : Type (u+1) := PLift α

#check @liftType.{0} Nat  -- List Nat : Type 1


def idd.{u} (α : Type u) (a : α) : α := a

def pair.{u, v} (α : Type u) (β : Type v) (a : α) (b : β) : α × β := (a, b)

#check @idd.{0}
#check @pair.{0, 0}


#check Nat → Bool -- : Type


def liftType1 (α : Type u) : Type (u+1) := PLift α

#check @liftType1 Nat


inductive Listy (α : Type u) : Type u where
  | nil : Listy α
  | cons : α → Listy α → Listy α

def mylist : Listy Nat :=
  .cons 2 (.cons 2 .nil)


inductive SumInflexible (x : Type u) (y : Type u) : Type u where
  | inl : x → SumInflexible x y
  | inr : y → SumInflexible x y

inductive SumFlexible (x : Type u) (y : Type v) : Type (max u v) where
  | inl : x → SumFlexible x y
  | inr : y → SumFlexible x y

def stringOrListString : SumFlexible String (List String) :=
  SumFlexible.inl "hello"

def truthValues : List Prop := [true, false, 1 + 2 = 3, 2 + 2 = 5]

theorem simple_prop : 1 = 1 := rfl
#check 1 = 1


def List.map' {α β : Type} (f : α → β) : List α → List β
  | []     => []
  | x :: xs => f x :: map f xs


def is_even (n : Nat) : Prop := ∃ k, n = 2 * k

def isPrime (n : Nat) : Prop := ∀ m : Nat, m > 1 → m < n → n % m ≠ 0

def lessThan (m n : Nat) : Prop := m < n

#check ∀ x, (Even x ∨ Odd x) ∧ ¬ (Even x ∧ Odd x)

#check ∀ x, (Even x ∨ Odd x) ∧ ¬ (Even x ∧ Odd x)
#check ∀ x, Even x ↔ 2 ∣ x
#check ∀ x, Even x → Even (x^2)
#check ∀ x, Even x ↔ Odd (x + 1)


local infix:50 " ≦ " => Nat.le
#check 3 ≦ 5

def reflexive {A : Type} (R : A → A → Prop) : Prop := ∀ a : A, R a a
def symmetric {A : Type} (R : A → A → Prop) : Prop := ∀ a b : A, R a b → R b a
def transitive {A : Type} (R : A → A → Prop) : Prop := ∀ a b c : A, R a b → R b c → R a c
def antisymmetric {A : Type} (R : A → A → Prop) : Prop := ∀ a b : A, R a b → R b a → a = b

def defEqual₁ : Nat :=
  7

def defEqual₂ : Nat :=
  Nat.succ (Nat.succ 5)

#eval defEqual₁  -- Output: 7
#eval defEqual₂  -- Output: 7


example : (λ x, x + x) 2 = 2 + 2 :=
rfl
