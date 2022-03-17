import tactic.induction
import data.int.basic
import data.set.basic

import .state .move

noncomputable theory
open_locale classical

def Angel_st (pw : ℕ) : Type :=
Π (s : State), angel_has_valid_move pw s.board → Valid_angel_move pw s.board

def Devil_st : Type :=
Π (s : State), Valid_devil_move s.board

instance {pw : ℕ} : inhabited (Angel_st pw) :=
⟨λ s h, ⟨h.some, h.some_spec⟩⟩

instance : inhabited Devil_st :=
⟨λ s, ⟨none, trivial⟩⟩