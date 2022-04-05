import tactic.induction
import data.int.basic
import data.set.basic

import .base .board

noncomputable theory
open_locale classical

instance : inhabited State := ⟨state₀⟩

@[reducible]
def State.len (s : State) : ℕ :=
s.history.length

def State.nth (s : State) (n : ℕ) : option Board :=
(s.history ++ [s.board]).nth n

-----

lemma hist_ne_of_hist_len_ne {s₁ s₂ : State}
  (h : s₁.len ≠ s₂.len) :
  s₁.history ≠ s₂.history :=
by { contrapose! h, rw [State.len, h] }

lemma hist_len_finish {s : State} :
  s.finish.len = s.len := rfl