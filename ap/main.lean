import tactic
import tactic.induction

import .defs .lemmas

theorem A_hws_iff_pw_ge_2 {pw : ℕ} :
  A_hws pw ↔ 2 ≤ pw :=
begin
  cases pw, simp [A_pw_0_not_hws],
  cases pw, simp [A_pw_1_not_hws], simp [nat.succ_le_succ],
  refine A_pw_ge_hws _ A_pw_2_hws, simp [nat.succ_le_succ],
end

theorem exi_pw_A_hws : ∃ (pw : ℕ), A_hws pw :=
⟨2, A_pw_2_hws⟩