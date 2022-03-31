import tactic.induction
import data.int.basic
import data.set.basic

import .board

noncomputable theory
open_locale classical

structure State : Type :=
(board : Board)
(history : list Board)
(act : Prop)

def init_state (b : Board) : State :=
{ board := b,
  history := [],
  act := true }

def state₀ : State :=
init_state board₀

instance : inhabited State := ⟨state₀⟩

def State.finish (s : State) : State :=
{s with act := false}