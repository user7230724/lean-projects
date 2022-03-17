import tactic.induction
import data.int.basic
import data.set.basic

noncomputable theory
open_locale classical

@[ext] structure Point : Type :=
(x y : ℤ)

def center : Point := ⟨0, 0⟩
instance : inhabited Point := ⟨center⟩