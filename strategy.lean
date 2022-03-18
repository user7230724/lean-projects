import tactic.induction
import data.int.basic
import data.set.basic

import .state .move

noncomputable theory
open_locale classical

def Angel (pw : ℕ) : Type :=
Π (s : State), angel_has_valid_move pw s.board → Valid_angel_move pw s.board

def Devil : Type :=
Π (s : State), Valid_devil_move s.board

instance {pw : ℕ} : inhabited (Angel pw) :=
⟨λ s h, ⟨h.some, h.some_spec⟩⟩

instance : inhabited Devil :=
⟨λ s, ⟨none, trivial⟩⟩