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

def T (a : Expr) :=
∃ (n : ℕ), (reduce^[n] a) = K

-----

def I := S ~ K ~ K

@[simp]
lemma not_T {a : Expr} : ¬T a ↔ ∀ (n : ℕ), ¬(reduce^[n]) a = K :=
by simp [T]

lemma T_K : T K :=
by { use 0, refl }

lemma not_T_S : ¬T S :=
begin
  simp, intro n, induction n,
  { simp },
  { simpa [function.iterate_succ_apply] },
end

lemma not_T_M : ¬T M :=
begin
  simp, intro n, induction n,
  { simp },
  { simpa [function.iterate_succ_apply] },
end