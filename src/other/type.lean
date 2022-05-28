import tactic
import tactic.induction

noncomputable theory
open_locale classical

inductive Nat : Type
| zero : Nat
| succ : Nat → Nat

def succ : Nat → Nat := Nat.succ

instance : has_zero Nat := ⟨Nat.zero⟩
instance : has_one Nat := ⟨succ 0⟩

def rec {t : Type} (z : t) (f : Nat → t → t) : Nat → t
| 0 := z
| (Nat.succ n) := f n (rec n)

-----

def Pf (n : Nat) : Prop := n = 1

lemma triv : Pf 1 :=
@rfl _ 1

lemma elim (P : Prop) (h : Pf 0) : P :=
by cases h

lemma psub (P : Nat → Prop) (n : Nat) (h₁ : Pf n) (h₂ : P 1) : P n :=
by { cases h₁, exact h₂ }

lemma ind (P : Nat → Prop) (h₁ : P 0) (h₂ : ∀ (n : Nat), P n → P (succ n)) (n : Nat) : P n :=
begin
  induction n with n ih,
  { exact h₁ },
  { exact h₂ n ih },
end

-----

def id' {t : Type} (a : t) : t := a
def const {t s : Type} (a : t) (b : s) : t := a

def cases {t : Type} (z : t) (f : Nat → t) (n : Nat) : t :=
rec z (λ k _, f k) n

def pred' (n : Nat) : Nat :=
cases 0 id n

def Prop' (p : Nat) : Nat :=
cases 1 (cases 1 (const 0)) p

def true' : Nat := 1
def false' : Nat := 0

def ite' {t : Type} (p : Nat) (a b : t) : t :=
cases b (const a) p

def not' (p : Nat) : Nat :=
ite' p false' true'

def and' (p q : Nat) : Nat :=
ite' p q false'

def or' (p q : Nat) : Nat :=
ite' p true' q

def imp (p q : Nat) : Nat :=
ite' p q true'

def iff' (p q : Nat) : Nat :=
ite' p q (not' q)

def nat_eq (a b : Nat) : Nat :=
rec not' (λ n f k, ite' k (f (pred' k)) 0) a b

-----

lemma elim' : ∀ (P : Prop) (n : Nat), Pf (succ (succ n)) → P :=
λ P n h, elim P (id psub (λ x, Pf (not' (pred' x))) _ h triv)

lemma cases' : ∀ (P : Nat → Prop), P 0 → (∀ (n : Nat), P (succ n)) → ∀ (n : Nat), P n :=
λ P h₁ h₂, ind P h₁ (λ n h₃, h₂ n)

lemma imp_intro' : ∀ (p q : Nat), Pf p → Pf q → Pf (imp p q) :=
λ p q h₁ h₂, id psub (λ x, Pf (imp x q)) _ h₁ h₂

-- lemma eq_of_nat_eq : ∀ (a b : Nat), Pf (nat_eq a b) → a = b :=
-- begin
--   apply ind (λ x, ∀ b, Pf (nat_eq x b) → x = b),
--   sorry {
--     apply cases' (λ x, Pf (nat_eq 0 x) → 0 = x),
--     {
--       intro h,
--       refl,
--     },
--     {
--       rintro n h,
--       apply elim _ h,
--     },
--   },
--   {
--     rintro a ih,
--     apply cases' (λ x, Pf (nat_eq (succ a) x) → succ a = x),
--     {
--       intro h,
--       apply elim _ h,
--     },
--     sorry,
--     -- b h,
--     -- specialize ih (pred' b),
--   },
-- end