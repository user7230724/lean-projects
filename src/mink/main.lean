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
| (a ~ b) := reduce a ~ b
| a := a

def R (e₁ e₂ : Expr) : Prop :=
∃ (n : ℕ), (reduce^[n]) e₁ = e₂

infix ` ==> `:50 := R

-----

@[refl]
lemma R.refl {a} : a ==> a :=
by use [0, rfl]

@[trans]
lemma R.trans {a b c} (h₁ : a ==> b) (h₂ : b ==> c) : a ==> c :=
begin
  cases h₁ with n₁ h₁, cases h₂ with n₂ h₂, use n₂ + n₁,
  rw function.iterate_add_apply, substs h₁ h₂,
end

lemma not_R {a b} : ¬a ==> b ↔ ∀ (n : ℕ), (reduce^[n]) a ≠ b :=
by simp [R]

-----

def term : Expr → Prop
| (_ ~ _) := false
| _ := true

def app (a : Expr) : Prop :=
¬term a

lemma term.induct {P : Expr → Prop} {a : Expr}
  (h₁ : term a) (h₂ : P K) (h₃ : P S) (h₄ : P M) : P a :=
by cases a; simp [*, term] at *

lemma R_iff_eq_of_reduce_eq_self {a b}
  (h : reduce a = a) : a ==> b ↔ a = b :=
begin
  split; intro h₁,
  { contrapose h₁, rw not_R, intro n, induction n with n ih,
    { tauto },
    { simp [h, ih] } },
  { subst h₁ },
end

lemma reduce_self_of_term {a} (h : term a) : reduce a = a :=
by apply term.induct h; refl

lemma R_iff_of_term {a b}
  (h : term a) : a ==> b ↔ a = b :=
R_iff_eq_of_reduce_eq_self (reduce_self_of_term h)

lemma reduce_arg_app_R_term {t f a a'}
  (h₁ : term t) (h₂ : a ==> a') :
  f ~ a ==> t ↔ f ~ a' ==> t :=
begin
  sorry
end

-----

def I := S ~ K ~ K

lemma I_id {a} : I ~ a ==> a :=
by use [2, rfl]