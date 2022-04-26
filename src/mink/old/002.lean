import tactic
import tactic.induction

noncomputable theory
open_locale classical

namespace test

inductive T
| nil : T
| pair : T → T → T
open T

@[reducible] def zero : T := nil
@[reducible] instance : has_zero T := ⟨nil⟩

@[reducible] def one : T := pair 0 0
@[reducible] instance : has_one T := ⟨one⟩

def is_nil : T → Prop
| nil := true
| (pair _ _) := false

def is_pair : T → Prop
| nil := false
| (pair _ _) := true

instance : has_coe_to_sort T Prop := ⟨is_pair⟩

-----

def True : T := 1
def False : T := 0

def Pro : T → T
| 0 := True
| 1 := True
| _ := False

def not : T → T
| nil := 1
| (pair _ _) := 0

def and : T → T → T
| 0 _ := 0
| _ a := 1

def or : T → T → T
| 0 a := a
| _ _ := 1

def iff : T → T → T
| 0 0 := True
| 1 1 := True
| _ _ := False

-----

lemma not_not {a : T} (h : Pro a) : iff (not (not a)) a := by
{
  replace h : a = 0 ∨ a = 1,
  {
    cases a with a b,
    { left, refl },
    {
      right,
      cases a, swap, { exact h.elim },
      cases b, swap, { exact h.elim },
      triv,
    },
  },
  rcases h with rfl | rfl; triv,
}

-----

end test