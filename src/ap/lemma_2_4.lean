import tactic
import tactic.induction

import .base .nice_D

noncomputable theory
open_locale classical

lemma lem_2_4 {pw N : ℕ}
  (h : ∃ (d : D), ∀ (a : A pw), A_trapped_in_for a d (Bounded N)) :
  ∃ (d : D), d.nice pw ∧ ∀ (a : A pw), A_trapped_in_for a d (Bounded N) :=
begin
  sorry
end