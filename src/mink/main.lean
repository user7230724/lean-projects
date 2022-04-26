import tactic
import tactic.induction

noncomputable theory
open_locale classical

inductive Expr : Type
| M : Expr
| K : Expr
| S : Expr
| App : Expr → Expr → Expr
open Expr

infixl ` ~ `:100 := App

inductive Reduce : Expr → Expr → Prop
| MK : Reduce (M ~ K) K
| MS : Reduce (M ~ S) S
| K {a b} : Reduce (K ~ a ~ b) a
| S {a b c} : Reduce (S ~ a ~ b ~ c) (a ~ c ~ (b ~ c))
| left {a b c} : Reduce a b → Reduce (a ~ c) (b ~ c)
| right {a b c} : Reduce a b → Reduce (c ~ a) (c ~ b)
| refl {a} : Reduce a a
| trans {a b c} : Reduce a b → Reduce b c → Reduce a c

infix ` ==> `:50 := Reduce

-----

@[refl]
lemma Reduce.refl' {a} : a ==> a :=
Reduce.refl

@[trans]
lemma Reduce.trans' {a b c} (h₁ : a ==> b) (h₂ : b ==> c) : a ==> c :=
Reduce.trans h₁ h₂

-----

