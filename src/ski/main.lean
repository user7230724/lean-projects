import tactic
import tactic.induction

noncomputable theory
open_locale classical

inductive Expr' : Type
| K' : Expr'
| S' : Expr'
| app' : Expr' → Expr' → Expr'
open Expr'

inductive Step : Expr' → Expr' → Prop
| k {a b} : Step (app' (app' K' a) b) a
| s {a b c} : Step (app' (app' (app' S' a) b) c) (app' (app' a c) (app' b c))
| func {a b c} : Step a b → Step (app' a c) (app' b c)
| arg {a b c} : Step a b → Step (app' c a) (app' c b)

def R := relation.refl_trans_gen Step

inductive Eq : Expr' → Expr' → Prop
| reduces {a b} : (∃ c, R a c ∧ R b c) → Eq a b
| ext {a b} : (∀ c, Eq (app' a c) (app' b c)) → Eq a b

lemma Eq.equivalence : equivalence Eq :=
begin
  sorry
end

-- #exit

instance : setoid Expr' := ⟨_, Eq.equivalence⟩

def Expr := quot Eq

def K : Expr := quot.mk _ K'
def S : Expr := quot.mk _ K'

def app (a b : Expr) : Expr :=
quot.mk _ (app' a.out b.out)

infixl ` ~ `:100 := app

def I := S ~ K ~ K

example {a b} : K ~ a ~ b = a :=
begin
  sorry
end