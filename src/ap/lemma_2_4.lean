import tactic
import tactic.induction

import .base .bounded .nice

noncomputable theory
open_locale classical

lemma lem_2_4 {pw N : ℕ}
  (h : ∃ (d : D), ∀ (a : A pw), A_trapped_in_for a d (bounded N)) :
  ∃ (d : D), d.nice pw ∧ ∀ (a : A pw), A_trapped_in_for a d (bounded N) :=
begin
  sorry
end