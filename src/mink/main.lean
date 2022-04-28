import tactic
import tactic.induction
import logic.function.iterate

noncomputable theory
open_locale classical

inductive Expr : Type
| K : Expr
| S : Expr
| M : Expr
| App : Expr → Expr → Expr
open Expr

infixl ` ~ `:100 := App

def reduce : Expr → Expr
| (K ~ a ~ b) := a
| (S ~ a ~ b ~ c) := a ~ c ~ (b ~ c)
| (M ~ K) := K
| (M ~ S) := S
| (M ~ a) := M ~ reduce a
| a := a

def R (e₁ e₂ : Expr) : Prop :=
∃ (n : ℕ), e₂ = (reduce^[n]) e₁

infix ` ==> `:50 := R

-----

@[refl]
lemma R.refl {a} : a ==> a :=
by use [0, rfl]

@[trans]
lemma R.trans' {a b c} (h₁ : a ==> b) (h₂ : b ==> c) : a ==> c :=
begin
  cases h₁ with n₁ h₁, cases h₂ with n₂ h₂, use n₂ + n₁,
  rw function.iterate_add_apply, substs h₁ h₂,
end

lemma not_R_iff {a b} : ¬a ==> b ↔ ∀ n, b ≠ (reduce^[n]) a :=
by simp [R]

-----

lemma R_iff_of_reduce_eq_self_iff {a b}
  (h : reduce a = a) : a ==> b ↔ a = b :=
begin
  split; intro h₁,
  { contrapose h₁, rw [not_R_iff], intro n, induction n with n ih,
    { tauto },
    { simp [h, ih] } },
  { subst h₁ },
end

-----

def I := S ~ K ~ K

lemma I_id {a} : I ~ a ==> a :=
by use [2, rfl]

-----

-- lemma not_reduces_of {α : Sort*} (f : α → Expr) {a b : Expr} {z : α}
--   (h₁ : f z = a)
--   (h₂ : ∀ (x : α), f x ≠ b → ???)
--   :
--   a /=> b :=
-- begin
--   sorry
-- end