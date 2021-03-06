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

-- lemma Eq.reflexive : reflexive Eq :=
-- by { intro a, left, use a, split; left }

-- lemma Eq.symmetric : symmetric Eq :=
-- begin
--   rintro a b h,
--   induction' h,
--   { left, tauto },
--   { right, exact ih },
-- end

lemma Eq.equivalence : equivalence Eq :=
begin
  refine ⟨_, _, _⟩,
  { intro a, left, use a, split; left },
  { rintro a b h,
    induction' h,
    { left, tauto },
    { right, exact ih }},
  {
    rintro a b x h₁ h₂,
    cases h₁ with _ _ h₁ _ _ h₁;
    cases h₂ with _ _ h₂ _ _ h₂,
    {
      left,
      rcases h₁ with ⟨c, hc₁, hc₂⟩,
      rcases h₂ with ⟨d, hd₁, hd₂⟩,
      sorry
    },
    sorry,
    sorry,
    sorry,
  },
end

-- #exit

instance : setoid Expr' := ⟨_, Eq.equivalence⟩

def Expr := quotient Expr'.setoid

def K : Expr := ⟦K'⟧
def S : Expr := ⟦S'⟧
def app (a b : Expr) : Expr := ⟦app' a.out b.out⟧
infixl ` ~ `:100 := app

def I := S ~ K ~ K

example {a b} : K ~ a ~ b = a :=
begin
  rw ←quotient.out_equiv_out,
  sorry
end