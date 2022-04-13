import tactic
import tactic.induction

noncomputable theory
open_locale classical

inductive Expr
| K : Expr
| S : Expr
| M : Expr
| Call : Expr → Expr → Expr
open Expr

infixl ` ~ `:100 := Call

inductive Reduces : Expr → Expr → Prop
| k (a b) : Reduces (K ~ a ~ b) a
| s (a b c) : Reduces (S ~ a ~ b ~ c) (a ~ c ~ (b ~ c))
| mk : Reduces (M ~ K) K
| ms : Reduces (M ~ S) S
| left {a b c} : Reduces a b → Reduces (a ~ c) (b ~ c)
| right {a b c} : Reduces a b → Reduces (c ~ a) (c ~ b)

inductive isK : Expr → Prop
| triv : isK K
| step {a b} (hr : Reduces a b) (hk : isK b) : isK a

-----

def I := S ~ K ~ K

inductive hasK : Expr → Prop
| triv : hasK K
| left (a b) : hasK a → hasK (a ~ b)
| right (a b) : hasK b → hasK (a ~ b)

lemma hasK_of_isK {a : Expr} (h : isK a) : hasK a :=
begin
  sorry
end

example : ¬isK (S ~ I ~ I ~ (S ~ I ~ I)) :=
begin
  sorry
end