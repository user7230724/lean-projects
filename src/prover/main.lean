import tactic
import tactic.induction

noncomputable theory
open_locale classical

namespace test

inductive nat : Type
| zero : nat
| succ : nat → nat

def succ : nat → nat := nat.succ

instance : has_zero nat := ⟨nat.zero⟩
instance : has_one nat := ⟨succ 0⟩

def rec {t : Type} (z : t) (f : nat → t → t) : nat → t
| nat.zero := z
| (nat.succ n) := f n (rec n)

-----

def Pf (n : nat) : Prop := n = 1

lemma triv : Pf 1 :=
@rfl _ 1

lemma elim (P : Prop) (h : Pf 0) : P :=
by cases h

lemma psub (P : nat → Prop) (n : nat) (h₁ : Pf n) (h₂ : P 1) : P n :=
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

def and (p q : nat) : nat :=
ite p q false

def or (p q : nat) : nat :=
ite p true q

def imp (p q : nat) : nat :=
ite p q true

def iff (p q : nat) : nat :=
ite p q (not q)

def nat_eq (a b : nat) : nat :=
rec not (λ n f k, ite k (f (pred k)) 0) a b

-----

lemma elim' : ∀ (P : Prop) (n : nat), Pf (succ (succ n)) → P :=
λ P n h, elim P (id psub (λ x, Pf (not (pred x))) _ h triv)

lemma cs : ∀ (P : nat → Prop), P 0 → (∀ (n : nat), P (succ n)) → ∀ (n : nat), P n :=
λ P h₁ h₂, ind P h₁ (λ n h₃, h₂ n)

lemma psub' : ∀ (P : nat → Prop) (n : nat), Pf n → P n → P 1 :=
λ P, cs (λ x, Pf x → P x → P 1) (λ h, elim _ h)
(cs (λ x, Pf (succ x) → P (succ x) → P 1) (λ h₁ h₂, h₂) (λ n h₁, elim' _ _ h₁))

lemma prop_cases : ∀ (P : nat → Prop), P true → P false → ∀ (n : nat), Pf (prop n) → P n :=
λ P h₁ h₂, cs (λ x, Pf (prop x) → P x) (λ _, h₂)
(cs (λ x, Pf (prop (succ x)) → P (succ x)) (λ _, h₁) (λ n h₃, elim _ h₃))

lemma imp_elim : ∀ (p q : nat), Pf (imp p q) → Pf p → Pf q :=
λ p q h₁ h₂, id psub' (λ x, Pf (imp x q)) _ h₂ h₁

lemma imp_intro : ∀ (p q : nat), Pf (prop p) → Pf (prop q) →
  (Pf p → Pf q) → Pf (imp p q) :=
λ p q hp hq, id prop_cases (λ x, (Pf x → Pf q) → Pf (imp x q)) (λ h, h triv) (λ h, triv) _ hp

lemma eq_refl : ∀ (a : nat), Pf (nat_eq a a) :=
ind (λ x, Pf (nat_eq x x)) triv (λ n ih, ih)

lemma prop_not : ∀ (a : nat), Pf (prop (not a)) :=
cs (λ x, Pf (prop (not x))) triv (λ a, triv)

lemma prop_nat_eq : ∀ (a b : nat), Pf (prop (nat_eq a b)) :=
ind (λ x, ∀ b, Pf (prop (nat_eq x b))) prop_not
(λ a ih, cs (λ x, Pf (prop (nat_eq (succ a) x))) triv (λ b, ih b))

lemma prop_prop : ∀ (a : nat), Pf (prop (prop a)) :=
cs (λ x, Pf (prop (prop x))) triv (cs (λ x, Pf (prop (prop (succ x)))) triv (λ n, triv))

lemma prop_imp : ∀ (p q : nat), Pf (prop q) → Pf (prop (imp p q)) :=
λ p q h, id cs (λ x, Pf (prop (imp x q))) triv (λ n, h) p

lemma prop_and : ∀ (p q : nat), Pf (prop q) → Pf (prop (and p q)) :=
λ p q h, id cs (λ x, Pf (prop (and x q))) triv (λ n, h) p

lemma prop_or : ∀ (p q : nat), Pf (prop q) → Pf (prop (or p q)) :=
λ p q h, id cs (λ x, Pf (prop (or x q))) h (λ n, triv) p

end test