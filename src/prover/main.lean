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

lemma prop_cs : ∀ (P : nat → Prop), P true → P false → ∀ (n : nat), prop n → P n :=
λ P h₁ h₂, cs (λ x, prop x → P x) (λ _, h₂)
(cs (λ x, prop (succ x) → P (succ x)) (λ _, h₁) (λ n h₃, elim _ h₃))

lemma imp_intro : ∀ (P Q : nat), prop P → prop Q → (P → Q) → imp P Q :=
λ P Q hp hq, id prop_cs (λ x, (x → Q) → imp x Q) (λ h, h triv) (λ h, triv) _ hp

lemma imp_elim : ∀ (P Q : nat), prop P → prop Q → imp P Q → P → Q :=
λ P Q _ _ h₁ h₂, id psub' (λ x, imp x Q) _ h₂ h₁

lemma eq_refl : ∀ (a : nat), nat_eq a a :=
ind (λ x, nat_eq x x) triv (λ n ih, ih)

lemma prop_prop : ∀ (a : nat), prop (prop a) :=
cs (λ x, prop (prop x)) triv (cs (λ x, prop (prop (succ x))) triv (λ n, triv))

lemma prop_not : ∀ (a : nat), prop (not a) :=
cs (λ x, prop (not x)) triv (λ a, triv)

lemma nat_eq_type : ∀ (a b : nat), prop (nat_eq a b) :=
ind (λ x, ∀ b, prop (nat_eq x b)) prop_not
(λ a ih, cs (λ x, prop (nat_eq (succ a) x)) triv (λ b, ih b))

lemma not_type : ∀ (a : nat), prop a → prop (not a) :=
λ a _, prop_not a

lemma imp_type : ∀ (P Q : nat), prop P → prop Q → prop (imp P Q) :=
λ P Q _ h, id cs (λ x, prop (imp x Q)) triv (λ n, h) P

lemma and_type : ∀ (P Q : nat), prop P → prop Q → prop (and P Q) :=
λ P Q _ h, id cs (λ x, prop (and x Q)) triv (λ n, h) P

lemma or_type : ∀ (P Q : nat), prop P → prop Q → prop (or P Q) :=
λ P Q _ h, id cs (λ x, prop (or x Q)) h (λ n, triv) P

lemma iff_type : ∀ (P Q : nat), prop P → prop Q → prop (iff P Q) :=
λ P Q h₁ h₂, id prop_cs (λ x, prop (iff x Q)) h₂ (not_type _ h₂) _ h₁

lemma and_intro : ∀ (P Q : nat), P → Q → and P Q :=
λ P Q h₁ h₂, id psub (λ x, and x Q) _ h₁ (id psub (λ x, and 1 x) _ h₂ triv)

lemma and_elim₁ : ∀ (P Q : nat), prop P → prop Q → and P Q → P :=
λ P Q h₁ h₂, id prop_cs (λ x, and x Q → x) (λ _, triv) (λ h, elim _ h) _ h₁

lemma and_elim₂ : ∀ (P Q : nat), prop P → prop Q → and P Q → Q :=
λ P Q h₁ h₂, id prop_cs (λ x, and x Q → Q) (λ h, h) (λ h, elim _ h) _ h₁

lemma or_intro₁ : ∀ (P Q : nat), P → prop Q → or P Q :=
λ P Q h₁ h₂, id psub (λ x, or x Q) _ h₁ triv

lemma or_intro₂ : ∀ (P Q : nat), prop P → Q → or P Q :=
λ P Q h₁ h₂, id prop_cs (λ x, or x Q) triv h₂ _ h₁

lemma or_elim : ∀ (F : Prop) (P Q : nat), prop P → prop Q → or P Q → (P → F) → (Q → F) → F :=
λ F P Q hp hq, prop_cs (λ x, or x Q → (x → F) → (Q → F) → F)
(λ h₁ h₂ h₃, h₂ triv) (λ h₁ h₂ h₃, h₃ h₁) _ hp

lemma iff_intro : ∀ (P Q : nat), prop P → prop Q → imp P Q → imp Q P → iff P Q :=
λ P Q hp hq, prop_cs (λ x, imp x Q → imp Q x → iff x Q) (λ h₁ h₂, h₁)
(λ h₁, prop_cs (λ x, imp x false → iff false x) (λ h₂, elim _ h₂) (λ _, triv) _ hq) _ hp

lemma iff_elim₁ : ∀ (P Q : nat), prop P → prop Q → iff P Q → imp P Q :=
λ P Q hp hq, prop_cs (λ x, iff x Q → imp x Q) (λ h, h) (λ _, triv) _ hp

lemma iff_elim₂ : ∀ (P Q : nat), prop P → prop Q → iff P Q → imp Q P :=
λ P Q hp hq, prop_cs (λ x, iff x Q → imp Q x)
(λ _, id prop_cs (λ x, imp x true) triv triv _ hq)
(id prop_cs (λ x, iff false x → imp x false) (λ h, h) (λ h, triv) _ hq) _ hp

lemma not_not : ∀ (P : nat), prop P → iff (not (not P)) P :=
prop_cs (λ x, iff (not (not x)) x) triv triv

lemma iff_sub : ∀ (F : nat → Prop) (P Q : nat), prop P → prop Q → iff P Q → F P → F Q :=
λ F P Q hp hq, prop_cs (λ x, iff x Q → F x → F Q)
(λ h₁ h₂, psub F Q (imp_elim true Q triv hq (iff_elim₁ true Q triv hq h₁) triv) h₂)
(id prop_cs (λ x, iff false x → F false → F x) (λ h, elim _ h) (λ _ h, h) _ hq) _ hp

lemma imp_refl : ∀ (P : nat), prop P → imp P P :=
λ P hp, imp_intro P P hp hp (λ h, h)

lemma iff_refl : ∀ (P : nat), prop P → iff P P :=
λ P hp, iff_intro P P hp hp (imp_refl P hp) (imp_refl P hp)

lemma and_symm : ∀ (P Q : nat), prop P → prop Q → and P Q → and Q P :=
λ P Q hp hq h, and_intro Q P (and_elim₂ _ _ hp hq h) (and_elim₁ _ _ hp hq h)

lemma or_symm : ∀ (P Q : nat), prop P → prop Q → or P Q → or Q P :=
λ P Q hp hq h, or_elim _ _ _ hp hq h (λ h₁, or_intro₂ _ _ hq h₁) (λ h₁, or_intro₁ _ _ h₁ hp)

lemma iff_symm : ∀ (P Q : nat), prop P → prop Q → iff P Q → iff Q P :=
λ P Q hp hq h, iff_intro _ _ hq hp (iff_elim₂ _ _ hp hq h) (iff_elim₁ _ _ hp hq h)

lemma imp_tran : ∀ (P Q R : nat), prop P → prop Q → prop R → imp P Q → imp Q R → imp P R :=
λ P Q R hp hq hr h₁ h₂, imp_intro _ _ hp hr
(λ h₃, imp_elim _ _ hq hr h₂ (imp_elim _ _ hp hq h₁ h₃))

-----

end test