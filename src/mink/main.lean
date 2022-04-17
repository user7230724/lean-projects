import tactic
import tactic.induction
import logic.function.iterate

inductive Expr
| K : Expr
| S : Expr
| M : Expr
| App : Expr → Expr → Expr
open Expr

infixl ` ~ `:100 := App

@[simp]
def reduce : Expr → Expr
| (K ~ a ~ b) := a
| (S ~ a ~ b ~ c) := a ~ c ~ (b ~ c)
| (M ~ K) := K
| (M ~ S) := S
| (M ~ a) := M ~ reduce a
| (a ~ b) := reduce a ~ b
| a := a

@[simp]
def reduces (a b : Expr) :=
∃ (n : ℕ), (reduce^[n] a) = b

infix ` ==> `:50 := reduces

def T (a : Expr) :=
reduces a K

-----

@[simp]
lemma not_T {a : Expr} : ¬T a ↔ ∀ (n : ℕ), ¬(reduce^[n]) a = K :=
by simp [T]

lemma reduce_succ {a : Expr} {n : ℕ} :
  (reduce^[n.succ]) a = (reduce^[n]) (reduce a) :=
by apply function.iterate_succ_apply

lemma reduce_succ' {a : Expr} {n : ℕ} :
  (reduce^[n.succ]) a = reduce (reduce^[n] a) :=
by apply function.iterate_succ_apply'

lemma T_K : T K :=
by { use 0, refl }

lemma not_T_of_reduce_id {a : Expr}
  (h₁ : a ≠ K) (h₂ : reduce a = a) : ¬T a := by
{ simp, intro n, induction n,
  { simpa },
  { simpa [h₂] }}

lemma not_T_S : ¬T S :=
by simp [not_T_of_reduce_id]

lemma not_T_M : ¬T M :=
by simp [not_T_of_reduce_id]

-----

@[reducible]
def I := S ~ K ~ K

@[simp]
lemma T_I_app_iff {a : Expr} : T (I ~ a) ↔ T a := by
{ split; rintro ⟨n, h⟩,
  { cases n, { cases h },
    cases n, { cases h },
    simp at h, use [n, h] },
  { use n + 2, simpa }}

lemma T_M_app_iff {a : Expr} : T (M ~ a) ↔ T a := by
{ split; rintro ⟨n, h⟩, cases n, { cases h }, use n, swap, use n + 1,
  repeat {
    induction' n with n ih; simp at *,
    { cases a; simp * at * },
    { cases a; simp at *; try { assumption },
      { contrapose! h, clear h ih, revert n,
        simp [←not_T, not_T_of_reduce_id] },
      { exact ih h }}}}

lemma not_T_of_reduce_app {a : Expr}
  (h : ∀ (n : ℕ), ∃ (b c : Expr), (reduce^[n]) a = b ~ c) : ¬T a :=
by { rw not_T, intro n, specialize h n, rcases h with ⟨b, c, h⟩, simp [h] }

lemma T_iff_T_reduces {a b : Expr} (h : a ==> b) : T a ↔ T b := by
{
  sorry
}

#exit

lemma not_T_SII_SII : ¬T (S ~ I ~ I ~ (S ~ I ~ I)) := by {
  apply not_T_of_reduce_app, intro n,
  induction n using nat.strong_induction_on with n ih, dsimp at ih,
  cases n; simp,
  cases n; simp,
  cases n; simp,
}