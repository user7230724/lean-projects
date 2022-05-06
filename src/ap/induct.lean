import tactic
import tactic.induction

import .base .game

noncomputable theory
open_locale classical

lemma induct_s_at {P : State → Prop} {pw n : ℕ} {g : Game pw}
  (h₁ : P g.s)
  (h₂ : ∀ {s : State} {ma},
  P s → A_move_valid pw s.board ma → P (apply_A_move s ma))
  (h₃ : ∀ {s : State} {md}, P s → D_move_valid s.board md → P (apply_D_move s md))
  (hf : ∀ {s : State}, P s → P s.finish) :
  P (g.play n).s :=
begin
  induction n with n ih,
  { assumption },
  { rw [play_at_succ'], let g₁ := _, change g.play n with g₁ at ih ⊢,
    rw Game.play_move, split_ifs with h₄, swap, { assumption },
    let a := g₁.a, let d := g₁.d,
    have h₅ : ∃ (s' : State), play_D_move_at g₁ h₄ = init_game a d s' ∧ P s',
    { let s' := apply_D_move g₁.s (d.f g₁.s h₄).m, use s',
      exact ⟨rfl, h₃ ih (d.f _ _).h⟩ },
    rcases h₅ with ⟨s', h₅, h₆⟩, rw h₅, clear h₅,
    rw play_A_move_at, split_ifs with h₅,
    { exact h₂ h₆ (a.f s' _ _).h },
    { exact hf h₆ }},
end

lemma induct_s {P : State → Prop} {pw : ℕ} {a : A pw} {d : D}
  (h₁ : P state₀)
  (h₂ : ∀ {s : State} {ma},
  P s → A_move_valid pw s.board ma → P (apply_A_move s ma))
  (h₃ : ∀ {s : State} {md}, P s → D_move_valid s.board md → P (apply_D_move s md))
  (hf : ∀ {s : State}, P s → P s.finish) :
  all_s a d P :=
by { intro n, apply induct_s_at; assumption }

lemma induct_b {P : Board → Prop} {pw : ℕ} {a : A pw} {d : D}
  (h₁ : P board₀)
  (h₂ : ∀ {b : Board} {ma}, P b → A_move_valid pw b ma → P (apply_A_move_b b ma))
  (h₃ : ∀ {b : Board} {md}, P b → D_move_valid b md → P (apply_D_move_b b md)) :
  all_b a d P :=
begin
  apply induct_s,
  { exact h₁ },
  { rintro s ma h₄ h₅, exact h₂ h₄ h₅ },
  { rintro s ma h₄ h₅, exact h₃ h₄ h₅ },
  { intro s, exact id },
end

lemma simulate_add {pw : ℕ} {a : A pw} {d : D} {n₁ n₂ : ℕ} :
  simulate a d (n₁ + n₂) = (simulate a d n₁).play n₂ :=
by { rw add_comm, apply function.iterate_add_apply }

lemma not_play_act_of_not_act {pw n : ℕ} {g : Game pw}
  (h : ¬g.act) : ¬(g.play n).act :=
by { apply @induct_s_at (λ s, ¬s.act); intros; assumption <|> exact not_false }

lemma act_of_act_play {pw n : ℕ} {g : Game pw}
  (h : (g.play n).act) : g.act :=
by { contrapose h, exact not_play_act_of_not_act h }

lemma play_eq_iff_states_eq {pw n : ℕ} {g : Game pw}
  (h : (g.play n).s = g.s) : g.play n = g :=
begin
  ext,
  { exact play_at_players_eq.1 },
  { exact play_at_players_eq.2 },
  { exact h },
end

lemma play_eq_of_not_act' {pw n : ℕ} {g : Game pw}
  (h : ¬g.act) : g.play n = g :=
begin
  rw play_eq_iff_states_eq, induction n with n ih,
  { refl },
  { rw play_at_succ',
    let g₁ : Game pw := _, change g.play n with g₁ at ih ⊢, have h₁ : ¬g₁.act,
    { change ¬g₁.s.act, rwa ih },
    rwa play_move_at_not_act h₁ },
end

lemma simulate_eq_of_not_act {pw n₁ n₂ : ℕ} {a : A pw} {d : D}
  (h₁ : ¬(simulate a d n₁).act)
  (h₂ : ¬(simulate a d n₂).act) :
  simulate a d n₁ = simulate a d n₂ :=
begin
  wlog h₃ : n₂ ≤ n₁,
  obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_le h₃,
  rw simulate_add at h₁ ⊢,
  let g : Game pw := _, change simulate a d n₂ with g at h₁ h₂ ⊢,
  exact play_eq_of_not_act' h₂,
end

lemma play_move_len_le {pw : ℕ} {g : Game pw} :
  g.play_move.s.len ≤ g.s.len + 2 :=
begin
  rw Game.play_move, split_ifs,
  { have h₁ : (play_D_move_at g h).s.len = g.s.len + 1,
    { rw hist_len_play_D_move_at },
    rw play_A_move_at, split_ifs with h₂,
    { rw [hist_len_play_A_move_at', h₁] },
    { change (play_D_move_at g h).s.finish.len ≤ _, rw [hist_len_finish, h₁],
      apply add_le_add_left, dec_trivial }},
  { exact le_add_right (le_refl _) },
end

lemma play_len_le {pw n : ℕ} {g : Game pw} :
  (g.play n).s.len ≤ g.s.len + n * 2 :=
begin
  induction n with n ih,
  { refl },
  { rw play_at_succ', let g₁ : Game pw := _, change g.play n with g₁ at ih ⊢,
    transitivity, exact play_move_len_le, rw [nat.succ_mul, ←add_assoc],
    apply add_le_add_right ih },
end

lemma simulate_len_le {pw n : ℕ} {a : A pw} {d : D} :
  (simulate a d n).s.len ≤ n * 2 :=
begin
  change ((simulate a d 0).play n).s.len ≤ n * 2 + (simulate a d 0).s.len,
  rw add_comm (n * 2), exact play_len_le,
end

lemma exi_A_wins_of_invariant {P : State → Prop} {pw : ℕ} {d : D} {s₀ : State}
  (h₀ : P s₀)
  (hP : ∀ (s : State), P s → s.act)
  (hm : ∀ (s s' : State) hs, P s → s' = apply_D_move s (d.f s hs).m →
    ∃ (ma : Valid_A_move pw s'.board), P (apply_A_move s' ma.m)) :
  ∃ (a : A pw), (init_game a d s₀).A_wins :=
begin
  let a : A pw,
  { refine ⟨λ s' hs' hvm, _⟩, refine (_ : ∃ (ma : Valid_A_move pw s'.board),
      ∀ (s : State) hs, P s → s' = apply_D_move s (d.f s hs).m →
      P (apply_A_move s' ma.m)).some,
    by_cases h₁ : ∃ (s : State) hs, P s ∧ s' = apply_D_move s (d.f s hs).m,
    { rcases h₁ with ⟨s, hs, h₁, h₂⟩, specialize hm s s' hs h₁ h₂,
      cases hm with ma hm, use ma, intros, assumption },
    { refine ⟨⟨_, hvm.some_spec⟩, _⟩, rintro s₁ hs₁ h₂ h₃, push_neg at h₁,
      specialize h₁ s₁ hs₁, push_neg at h₁, specialize h₁ h₂, contradiction }},
  use a, rintro n, apply hP, induction n with n ih,
  { assumption },
  { rw play_at_succ', let g : Game pw := _,
    change (init_game a d s₀).play n with g at ih ⊢,
    have hs := hP _ ih, rw play_move_at_act hs, let s := g.s,
    let s' := apply_D_move s (d.f s hs).m,
    have h₁ : play_D_move_at g hs = init_game a d s',
    { ext,
      { exact play_at_players_eq.1 },
      { exact play_at_players_eq.2 },
      { change apply_D_move _ _ = apply_D_move _ _, congr,
        exact play_at_players_eq.2 }},
    rw h₁, clear h₁, have hvm : A_has_valid_move pw s'.board,
    { specialize hm s s' hs ih rfl, cases hm with ma hma, exact ⟨_, ma.h⟩ },
    rw [play_A_move_at, dif_pos], swap, { split; assumption },
    change P (apply_A_move s' (a.f s' hs hvm).m),
    generalize hma : a.f s' hs hvm = ma,
    change Exists.some _ = _ at hma, generalize_proofs h₁ at hma,
    have h₂ := h₁.some_spec s hs ih rfl, subst hma, assumption },
end

lemma play_eq_of_not_act {pw n k : ℕ} {a : A pw} {d : D} {s : State}
  (h₁ : ¬((init_game a d s).play n).act)
  (h₂ : ¬((init_game a d s).play k).act) :
  (init_game a d s).play n = (init_game a d s).play k :=
begin
  wlog h₃ : k ≤ n, obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_le h₃,
  rw play_add, exact play_eq_of_not_act' h₂,
end

lemma not_act_of_descend (f : State → ℕ) (P : State → Prop)
  {pw n : ℕ} {a : A pw} {d : D} {s₀ : State}
  (hp₀ : f s₀ < n)
  (hp₁ : P s₀)
  (hp₂ : ∀ (s s' : State) hs hs' hvm, P s → s' = apply_D_move s (d.f s hs).m →
    P (apply_A_move s' (a.f s' hs' hvm).m))
  (hp₃ : ∀ (s s' : State) hs hs' hvm, P s → s' = apply_D_move s (d.f s hs).m →
    f (apply_A_move s' (a.f s' hs' hvm).m) < f s) :
  ¬((init_game a d s₀).play n).act :=
begin
  have h₀ : ∀ (n : ℕ) (s : State), s = ((init_game a d s₀).play n).s →
    s.act → P s,
  { clear' hp₀ n, rintro n _ rfl hs₁,
    rw ←Game.act at hs₁, induction n with n ih,
    { exact hp₁ },
    { rw play_at_succ' at hs₁ ⊢, let g : Game pw := _,
      change (init_game a d s₀).play n with g at ih hs₁ ⊢,
      obtain ⟨s', hs, hs', hvm, h₁, h₂⟩ :=
        play_move_state_eq_of_act_play_move hs₁, rw h₂,
      have ha : g.a = a := play_at_players_eq.1, rw ha at *, clear ha,
      have hd : g.d = d := play_at_players_eq.2, rw hd at *, clear hd,
      apply hp₂,
      { exact ih hs },
      { exact h₁ }}},
  suffices h : ∀ (n : ℕ) (s : State), s = ((init_game a d s₀).play n).s →
    s.act → f s + n ≤ f s₀,
  { apply mt (h n _ rfl), push_neg, apply nat.lt_add_left, exact hp₀ },
  clear' n hp₀, rintro n _ rfl hs₁, induction n with n ih,
  { refl },
  { rw play_at_succ' at hs₁ ⊢, let g : Game pw := _,
    change (init_game a d s₀).play n with g at ih hs₁ ⊢,
    obtain ⟨s', hs, hs', hvm, h₁, h₂⟩ :=
      play_move_state_eq_of_act_play_move hs₁, rw h₂,
    have ha : g.a = a := play_at_players_eq.1, rw ha at *, clear ha,
    have hd : g.d = d := play_at_players_eq.2, rw hd at *, clear hd,
    specialize ih hs,
    have h : f (apply_A_move s' (a.f s' hs' hvm).m) < f g.s,
    { apply hp₃,
      { apply h₀,
        { refl },
        { exact hs } },
      { exact h₁ }},
    replace h : f (apply_A_move s' (a.f s' hs' hvm).m) + n < f g.s + n,
    { exact add_lt_add_right h n },
    rw ←nat.succ_le_iff at h, rw nat.add_succ, exact h.trans ih },
end

lemma not_act_of_descend_single_moves (f : State → ℕ) (P : State → Prop)
  {pw n : ℕ} {a : A pw} {d : D} {s₀ : State}
  (hp₀ : f s₀ < n)
  (hp₁ : P s₀)
  (hp₂ : ∀ (s : State) hs hvm, P s → P (apply_A_move s (a.f s hs hvm).m))
  (hp₃ : ∀ (s : State) hs, P s → P (apply_D_move s (d.f s hs).m))
  (hp₄ : ∀ (s : State) hs hvm, P s → f (apply_A_move s (a.f s hs hvm).m) ≤ f s)
  (hp₅ : ∀ (s : State) hs, P s → f (apply_D_move s (d.f s hs).m) < f s) :
  ¬((init_game a d s₀).play n).act :=
begin
  apply not_act_of_descend f P hp₀ hp₁,
  { rintro s s' hs hs' hvm h₁ rfl, apply hp₂, apply hp₃, exact h₁ },
  { rintro s s' hs hs' hvm h₁ h₂, let s₁ : State := _, change f s₁ < _,
    have h₃ : f s' < f s,
    { subst s', apply hp₅, exact h₁ },
    have h₄ : f s₁ ≤ f s',
    { subst s', apply hp₄, apply hp₃, exact h₁ },
    exact gt_of_gt_of_ge h₃ h₄ },
end

lemma not_act_of_descend_play_move' (f : State → ℕ) (P : State → Prop)
  {pw n : ℕ} {a : A pw} {d : D} {s₀ : State}
  (hp₀ : f s₀ < n)
  (hp₁ : P s₀)
  (hp₂ : ∀ (g : Game pw), g.play_move.act → P g.s → P g.play_move.s)
  (hp₃ : ∀ (g : Game pw), g.play_move.act → P g.s → f g.play_move.s < f g.s) :
  ¬((init_game a d s₀).play n).act :=
begin
  have h : ∀ (Q : State → State → Prop),
    (∀ (g : Game pw), g.play_move.act → P g.s → Q g.s g.play_move.s) →
    ∀ (s s' : State) hs hs' hvm, P s → s' = apply_D_move s (d.f s hs).m →
    Q s (apply_A_move s' (a.f s' hs' hvm).m),
  { rintro Q hQ, rintro s s' hs hs' hvm h₁ h₂,
    have hs₁ : (init_game a d s).play_move.act,
    { subst s', exact act_play_move_of_A_hvm hvm },
    specialize hQ (init_game a d s) hs₁ h₁,
    obtain ⟨s', hs, hs', hvm, h₃, h₄⟩ := play_move_state_eq_of_act_play_move hs₁,
    rw h₄ at hQ, subst_vars, exact hQ },
  apply not_act_of_descend f P hp₀ hp₁,
  { exact h (λ (s₁ s₂ : State), P s₂) hp₂ },
  { exact h (λ (s₁ s₂ : State), f s₂ < f s₁) hp₃ },
end

lemma not_act_of_descend_play_move (f : State → ℕ) (P : State → Prop)
  {pw n : ℕ} {a : A pw} {d : D} {s₀ : State}
  (hp₀ : f s₀ < n)
  (hp₁ : P s₀)
  (hp₂ : ∀ (s : State), (init_game a d s).play_move.act → P s →
    P (init_game a d s).play_move.s)
  (hp₃ : ∀ (s : State), (init_game a d s).play_move.act → P s →
    f (init_game a d s).play_move.s < f s) :
  ¬((init_game a d s₀).play n).act :=
begin
  have h : ∀ (Q : State → State → Prop),
    (∀ (s : State), (init_game a d s).play_move.act → P s →
      Q s (init_game a d s).play_move.s) →
    ∀ (s s' : State) hs hs' hvm, P s → s' = apply_D_move s (d.f s hs).m →
    Q s (apply_A_move s' (a.f s' hs' hvm).m),
  { rintro Q hQ, rintro s s' hs hs' hvm h₁ h₂,
    have hs₁ : (init_game a d s).play_move.act,
    { subst s', exact act_play_move_of_A_hvm hvm },
    specialize hQ s hs₁ h₁,
    obtain ⟨s', hs, hs', hvm, h₃, h₄⟩ := play_move_state_eq_of_act_play_move hs₁,
    rw h₄ at hQ, subst_vars, exact hQ },
  apply not_act_of_descend f P hp₀ hp₁,
  { exact h (λ (s₁ s₂ : State), P s₂) hp₂ },
  { exact h (λ (s₁ s₂ : State), f s₂ < f s₁) hp₃ },
end