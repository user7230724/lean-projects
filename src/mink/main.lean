import tactic
import tactic.induction

noncomputable theory
open_locale classical

inductive Expr
| Bot : Expr
| K : Expr
| S : Expr
| M : Expr
| Call : Expr → Expr → Expr
open Expr

instance : has_bot Expr := ⟨Bot⟩

infixl ~:100 := Call

inductive Reduces : Expr → Expr → Prop
| bot (a) : Reduces (⊥ ~ a) ⊥
| k (a b) : Reduces (K ~ a ~ b) a
| s (a b c) : Reduces (S ~ a ~ b ~ c) (a ~ c ~ (b ~ c))
| mb : Reduces (M ~ ⊥) ⊥
| mk : Reduces (M ~ K) K
| ms : Reduces (M ~ S) S
| mm : Reduces (M ~ M) ⊥
| call {a b c} (h₁ : Reduces a b) : Reduces (a ~ c) (b ~ c)

inductive isK : Expr → Prop
| triv : isK K
| step {a b} (hr : Reduces a b) (hk : isK b) : isK a

-----

def I := S ~ K ~ K

example : ¬isK (S ~ I ~ I ~ (S ~ I ~ I)) :=
begin
  sorry
end