import tactic
import tactic.induction
import logic.function.iterate

noncomputable theory
open_locale classical

inductive Expr : Type
| K : Expr
| S : Expr
| M : Expr
| app : Expr → Expr → Expr
open Expr

infixl ` ~ `:100 := app

instance : inhabited Expr := ⟨K⟩

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

local infix ` > `:50 := reduces

-----

@[refl]
lemma reduces.refl {a} : a > a :=
by use [0, rfl]

@[trans]
lemma reduces.trans {a b c} (h₁ : a > b) (h₂ : b > c) : a > c :=
begin
  cases h₁ with n₁ h₁, cases h₂ with n₂ h₂, use n₂ + n₁,
  rw function.iterate_add_apply, substs h₁ h₂,
end

lemma not_reduces {a b} : ¬a > b ↔ ∀ (n : ℕ), (step^[n]) a ≠ b :=
by simp [reduces]

-----

def Expr.comb : Expr → Prop
| (_ ~ _) := false
| _ := true

lemma term_induct {P : Expr → Prop} {a : Expr}
  (h₁ : a.comb) (h₂ : P K) (h₃ : P S) (h₄ : P M) : P a :=
by cases a; simp [*, Expr.comb] at *

lemma reduces_iff_eq_of_step_eq_self {a b}
  (h : step a = a) : a > b ↔ a = b :=
begin
  split; intro h₁,
  { contrapose h₁, rw not_reduces, intro n, induction n with n ih,
    { tauto },
    { simp [h, ih] } },
  { subst h₁ },
end

lemma step_self_of_term {a : Expr} (h : a.comb) : step a = a :=
by apply term_induct h; refl

lemma reduces_iff_of_term {a b : Expr}
  (h : a.comb) : a > b ↔ a = b :=
reduces_iff_eq_of_step_eq_self (step_self_of_term h)

-----

lemma apps_reduce_iff_args_reduce {t f : Expr} {args : list (Expr × Expr)}
  (h₁ : t.comb)
  (h₂ : ∀ (p : Expr × Expr), p ∈ args → p.1 > p.2) :
  function.uncurry (λ a b, a > t ↔ b > t)
    (list.foldl (λ (a p : Expr × Expr), (a.1 ~ p.1, a.2 ~ p.2)) ⟨f, f⟩ args) :=
begin
  let m : Expr × Expr := _,
  change function.uncurry _ m,
  change _ ↔ _,
  simp_rw reduces,
  sorry
end

lemma app_reduces_iff_arg_reduces {t f a b : Expr}
  (h₁ : t.comb)
  (h₂ : a > b) :
  f ~ a > t ↔ f ~ b > t :=
begin
  apply @apps_reduce_iff_args_reduce t f [(a, b)] h₁,
  rintro p h₄, rw list.mem_singleton at h₄, subst p, exact h₂,
end

-----

def I := S ~ K ~ K

lemma I_id {a} : I ~ a > a :=
⟨2, rfl⟩

-----

def Expr.mk_diff (a : Expr) : Expr :=
K ~ a

lemma mk_diff_ne {a : Expr} : a.mk_diff ≠ a :=
by { rw Expr.mk_diff, induction' a; simp, rintro rfl, assumption }

-----

-- def func_coe_raw

-- inductive Func : (Expr → Expr) → Expr → Prop
-- | id : Func id I
-- | comb {a : Expr} : a.comb → Func (λ _, a) (K ~ a)
-- | app {f₁ f₂ : Expr → Expr} {e₁ e₂ : Expr} :
--   Func f₁ e₁ → Func f₂ e₂ → Func (λ a, f₁ a ~ f₂ a) (S ~ e₁ ~ e₂)

-- def func_coe_raw (f : Expr → Expr) : Expr :=
-- if h : ∃ (e : Expr), Func f e then h.some else default

-- lemma exi_func_coe : ∃ (f : (Expr → Expr) → Expr),
--   (f id = I) ∧
--   (∀ (a : Expr), a.comb → f (λ _, a) = K ~ a) ∧
--   (∀ (g₁ g₂ : Expr → Expr), f (λ a, g₁ a ~ g₂ a) = S ~ f g₁ ~ f g₂) :=
-- begin
--   refine ⟨func_coe_raw, _, _, _⟩; simp_rw func_coe_raw,
--   sorry {
--     rw dif_pos, swap,
--     {
--       use I,
--       exact Func.id,
--     },
--     generalize_proofs h,
--     have h₁ := h.some_spec,
--     induction' h₁,
--     {
--       refl,
--     },
--     {
--       cases mk_diff_ne (congr_fun induction_eq h.some.mk_diff).symm,
--     },
--     {
--       cases congr_fun induction_eq K,
--     },
--   },
--   sorry {
--     rintro a h,
--     rw dif_pos, swap,
--     {
--       use K ~ a,
--       exact Func.comb h,
--     },
--     generalize_proofs h₁,
--     have h₂ := h₁.some_spec,
--     induction' h₂,
--     {
--       cases congr_fun induction_eq (K ~ K),
--       cases h,
--     },
--     {
--       cases congr_fun induction_eq K,
--       refl,
--     },
--     {
--       cases congr_fun induction_eq K,
--       cases h,
--     },
--   },
--   {
--     rintro g₁ g₂,
--     rw dif_pos,
--   },
-- end

-----