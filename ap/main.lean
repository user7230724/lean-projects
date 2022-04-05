import tactic
import tactic.induction

import .defs .lemmas

theorem angel_hws_iff_pw_ge_2 {pw : ℕ} :
  angel_hws pw ↔ 2 ≤ pw :=
begin
  cases pw, simp [angel_pw_0_not_hws],
  cases pw, simp [angel_pw_1_not_hws], simp [nat.succ_le_succ],
  refine angel_pw_ge_hws _ angel_pw_2_hws, simp [nat.succ_le_succ],
end

theorem exi_pw_angel_hws : ∃ (pw : ℕ), angel_hws pw :=
⟨2, angel_pw_2_hws⟩