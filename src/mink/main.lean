import tactic
import tactic.induction

noncomputable theory
open_locale classical

inductive Expr
| K : Expr
| S : Expr
| M : Expr
| App : Expr → Expr → Expr
open Expr

infixl ` ~ `:100 := App

inductive Reduces : Expr → Expr → Prop
| refl {a} : Reduces a a
| trans {a b c} : Reduces a b → Reduces b c → Reduces a c
| k {a b} : Reduces (K ~ a ~ b) a
| s {a b c} : Reduces (S ~ a ~ b ~ c) (a ~ c ~ (b ~ c))
| mk : Reduces (M ~ K) K
| ms : Reduces (M ~ S) S
| left {a b c} : Reduces a b → Reduces (a ~ c) (b ~ c)
| right {a b c} : Reduces a b → Reduces (c ~ a) (c ~ b)

infix ` ==> `:50 := Reduces

-----

def I := S ~ K ~ K

@[refl]
lemma reduces_refl {a : Expr} : a ==> a :=
Reduces.refl

@[trans]
lemma reduces_trans {a b c : Expr} (h₁ : a ==> b) (h₂ : b ==> c) : a ==> c :=
h₁.trans h₂

lemma K_reduces_to_iff_eq_K {a : Expr} : K ==> a ↔ a = K :=
begin
  split; intro h,
  { induction' h,
    { refl },
    { subst b, apply ih_h, refl }},
  { subst h },
end

lemma not_K_reduces_S : ¬K ==> S :=
by simp [K_reduces_to_iff_eq_K]

lemma I_app_reduces_to_self {a : Expr} : I ~ a ==> a :=
begin
  transitivity, apply Reduces.s,
  transitivity, apply Reduces.k,
  refl,
end

-----

-- meta def reduce' : Expr → option Expr
-- | (K ~ a ~ b) := some a
-- | (S ~ a ~ b ~ c) := some (a ~ c ~ (b ~ c))
-- | (M ~ K) := some K
-- | (M ~ S) := some S
-- | _ := none

-- meta def reduce : Expr → Expr
-- | e@(a ~ b) := match reduce' e with
--   | some e₁ := reduce e₁
--   | none := match reduce' a with
--     | some a₁ := reduce (a₁ ~ b)
--     | none := e
--   end
-- end
-- | a := a