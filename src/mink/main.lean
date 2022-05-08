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

def step : Expr → Expr
| (K ~ a ~ b) := a
| (S ~ a ~ b ~ c) := a ~ c ~ (b ~ c)
| (M ~ K) := K
| (M ~ S) := S
| (M ~ a) := M ~ step a
| (a ~ b) := step a ~ b
| a := a

def reduces (e₁ e₂ : Expr) : Prop :=
∃ (n : ℕ), (step^[n]) e₁ = e₂

infix ` ⇝ `:50 := reduces

-----

@[refl]
lemma reduces.refl {a} : a ⇝ a :=
by use [0, rfl]

@[trans]
lemma reduces.trans {a b c} (h₁ : a ⇝ b) (h₂ : b ⇝ c) : a ⇝ c :=
begin
  cases h₁ with n₁ h₁, cases h₂ with n₂ h₂, use n₂ + n₁,
  rw function.iterate_add_apply, substs h₁ h₂,
end

lemma not_reduces {a b} : ¬a ⇝ b ↔ ∀ (n : ℕ), (step^[n]) a ≠ b :=
by simp [reduces]

-----

def term : Expr → Prop
| (_ ~ _) := false
| _ := true

def app (a : Expr) : Prop :=
¬term a

lemma term.induct {P : Expr → Prop} {a : Expr}
  (h₁ : term a) (h₂ : P K) (h₃ : P S) (h₄ : P M) : P a :=
by cases a; simp [*, term] at *

lemma reduces_iff_eq_of_step_eq_self {a b}
  (h : step a = a) : a ⇝ b ↔ a = b :=
begin
  split; intro h₁,
  { contrapose h₁, rw not_reduces, intro n, induction n with n ih,
    { tauto },
    { simp [h, ih] } },
  { subst h₁ },
end

lemma step_self_of_term {a} (h : term a) : step a = a :=
by apply term.induct h; refl

lemma reduces_iff_of_term {a b}
  (h : term a) : a ⇝ b ↔ a = b :=
reduces_iff_eq_of_step_eq_self (step_self_of_term h)

-----

lemma apps_reduce_iff_args_reduce {t f : Expr} {args : list (Expr × Expr)}
  (h₁ : term t)
  (h₂ : ∀ (p : Expr × Expr), p ∈ args → p.1 ⇝ p.2) :
  function.uncurry (λ a b, a ⇝ t ↔ b ⇝ t)
    (list.foldl (λ (a p : Expr × Expr), (a.1 ~ p.1, a.2 ~ p.2)) ⟨f, f⟩ args) :=
begin
  let m : Expr × Expr := _,
  change function.uncurry _ m,
  change _ ↔ _,
  simp_rw reduces,
  sorry
end

lemma app_reduces_iff_arg_reduces {t f a b}
  (h₁ : term t)
  (h₂ : a ⇝ b) :
  f ~ a ⇝ t ↔ f ~ b ⇝ t :=
begin
  apply @apps_reduce_iff_args_reduce t f [(a, b)] h₁ _, rintro p h₄,
  rw list.mem_singleton at h₄, subst p, exact h₂,
end

-----

def I := S ~ K ~ K

lemma I_id {a} : I ~ a ⇝ a :=
by use [2, rfl]