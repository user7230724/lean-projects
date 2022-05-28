import tactic
import tactic.induction

noncomputable theory
open_locale classical

namespace test

inductive nat : Type
| zero : nat
| succ : nat → nat

def succ : nat → nat := nat.succ

def rec {t : Type} (z : t) (f : nat → t → t) : nat → t
| nat.zero := z
| (nat.succ n) := f n (rec n)

instance : has_zero nat := ⟨nat.zero⟩
instance : has_one nat := ⟨succ 0⟩

-----

instance : has_coe_to_sort nat Prop := ⟨λ n, n = 1⟩

lemma triv : (1 : nat) :=
@rfl _ 1

lemma elim (P : Prop) (h : (0 : nat)) : P :=
by cases h

lemma psub (P : nat → Prop) (n : nat) (h₁ : n) (h₂ : P 1) : P n :=
by { cases h₁, exact h₂ }

lemma ind (P : nat → Prop) (h₁ : P 0) (h₂ : ∀ (n : nat), P n → P (succ n)) (n : nat) : P n :=
begin
  induction n with n ih,
  { exact h₁ },
  { exact h₂ n ih },
end

-----

def id' {t : Type} (a : t) : t := a
def const {t s : Type} (a : t) (b : s) : t := a

def cases {t : Type} (z : t) (f : nat → t) (n : nat) : t :=
rec z (λ k _, f k) n

def pred (n : nat) : nat :=
cases 0 id n

def prop (p : nat) : nat :=
cases 1 (cases 1 (const 0)) p

def true : nat := 1
def false : nat := 0

def ite {t : Type} (p : nat) (a b : t) : t :=
cases b (const a) p

def not (p : nat) : nat :=
ite p false true

def and (P Q : nat) : nat :=
ite P Q false

def or (P Q : nat) : nat :=
ite P true Q

def imp (P Q : nat) : nat :=
ite P Q true

def iff (P Q : nat) : nat :=
ite P Q (not Q)

def nat_eq (a b : nat) : nat :=
rec not (λ n f k, ite k (f (pred k)) 0) a b

-----

lemma elim' : ∀ (P : Prop) (n : nat), succ (succ n) → P :=
λ P n h, elim P (id psub (λ x, not (pred x)) _ h triv)

lemma cs : ∀ (P : nat → Prop), P 0 → (∀ (n : nat), P (succ n)) → ∀ (n : nat), P n :=
λ P h₁ h₂, ind P h₁ (λ n h₃, h₂ n)

lemma psub' : ∀ (P : nat → Prop) (n : nat), n → P n → P 1 :=
λ P, cs (λ x, x → P x → P 1) (λ h, elim _ h)
(cs (λ x, succ x → P (succ x) → P 1) (λ h₁ h₂, h₂) (λ n h₁, elim' _ _ h₁))

lemma prop_cases : ∀ (P : nat → Prop), P true → P false → ∀ (n : nat), prop n → P n :=
λ P h₁ h₂, cs (λ x, prop x → P x) (λ _, h₂)
(cs (λ x, prop (succ x) → P (succ x)) (λ _, h₁) (λ n h₃, elim _ h₃))

lemma imp_elim : ∀ (P Q : nat), imp P Q → P → Q :=
λ P Q h₁ h₂, id psub' (λ x, imp x Q) _ h₂ h₁

lemma imp_intro : ∀ (P Q : nat), prop P → prop Q →
  (P → Q) → imp P Q :=
λ P Q hp hq, id prop_cases (λ x, (x → Q) → imp x Q) (λ h, h triv) (λ h, triv) _ hp

lemma eq_refl : ∀ (a : nat), nat_eq a a :=
ind (λ x, nat_eq x x) triv (λ n ih, ih)

lemma prop_not : ∀ (a : nat), prop (not a) :=
cs (λ x, prop (not x)) triv (λ a, triv)

lemma prop_nat_eq : ∀ (a b : nat), prop (nat_eq a b) :=
ind (λ x, ∀ b, prop (nat_eq x b)) prop_not
(λ a ih, cs (λ x, prop (nat_eq (succ a) x)) triv (λ b, ih b))

lemma prop_prop : ∀ (a : nat), prop (prop a) :=
cs (λ x, prop (prop x)) triv (cs (λ x, prop (prop (succ x))) triv (λ n, triv))

lemma prop_imp : ∀ (P Q : nat), prop Q → prop (imp P Q) :=
λ P Q h, id cs (λ x, prop (imp x Q)) triv (λ n, h) P

lemma prop_and : ∀ (P Q : nat), prop Q → prop (and P Q) :=
λ P Q h, id cs (λ x, prop (and x Q)) triv (λ n, h) P

lemma prop_or : ∀ (P Q : nat), prop Q → prop (or P Q) :=
λ P Q h, id cs (λ x, prop (or x Q)) h (λ n, triv) P

end test