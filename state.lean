import tactic.induction
import data.int.basic
import data.set.basic

import .board

noncomputable theory
open_locale classical

structure State : Type :=
(board : Board)
(history : list Board)

def state₀ : State := ⟨board₀, []⟩
instance : inhabited State := ⟨state₀⟩