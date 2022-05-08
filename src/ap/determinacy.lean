import tactic.induction
import data.int.basic
import data.set.basic
import logic.function.iterate

import .defs .game .played_move

noncomputable theory
open_locale classical

lemma not_A_hws_at_of {pw : ℕ} {s : State}
  (h : D_hws_at pw s) : ¬A_hws_at pw s :=
begin
  cases h with d h, change ¬∃ _, _, push_neg,
  intro a, use d, rw not_A_wins_at, apply h,
end

lemma not_D_hws_at_of {pw : ℕ} {s : State}
  (h : A_hws_at pw s) : ¬D_hws_at pw s :=
begin
  cases h with d h, change ¬∃ _, _, push_neg,
  intro a, use d, rw not_D_wins_at, apply h,
end

-----

lemma act_of_not_D_hws {pw : ℕ} {s : State}
  (h : ¬D_hws_at pw s) : s.act :=
by { contrapose! h, use default, intro a, use 0 }

lemma A_hvm_of_not_D_hws {pw : ℕ} {s : State}
  (h : ¬D_hws_at pw s) :
  ∀ (md : Valid_D_move s.board),
  A_has_valid_move pw (apply_D_move s md.m).board :=
begin
  intro md, rw D_hws_at at h, push_neg at h,
  let d := (default : D).set_move s md, specialize h d,
  cases h with a h, rw not_D_wins_at at h, specialize h 1, rw play_1 at h,
  rw Game.play_move at h, split_ifs at h with h₁, swap, { contradiction }, 
  rw play_A_move_at at h, split_ifs at h with h₂, swap, { cases h },
  cases h₂ with h₂ h₃, convert h₃, change _ = dite _ _ _, rw dif_pos; refl,
end

lemma exi_moves_hws_of_not_D_hws {pw : ℕ} {s : State}
  (h : ¬D_hws_at pw s) :
  ∀ (md : Valid_D_move s.board) (d : D),
  ∃ (ma : Valid_A_move pw (apply_D_move s md.m).board) (a : A pw),
  (init_game a d (apply_A_move (apply_D_move s md.m) ma.m)).A_wins :=
begin
  have hs : s.act := act_of_not_D_hws h,
  have h₁ : ¬∃ _, _ := h, push_neg at h₁,
  simp_rw not_D_wins_at at h₁, rintro md d₀, let md₀ := d₀.f s hs,
  let d := d₀.set_move s md, let s' := apply_D_move s md.m,
  change apply_D_move s md.m with s',
  have h₂ : A_has_valid_move pw s'.board,
  { apply A_hvm_of_not_D_hws h },
  specialize h₁ d, cases h₁ with a h₁, let ma := a.f s' hs h₂, use [ma, a],
  have hh : d₀ = d.set_move s md₀,
  { change d₀ = (d₀.set_move s md).set_move s md₀,
    rw [D_set_move_set_move_eq, D_set_move_self] },
  rw hh, have h₃ : (init_game a d (apply_A_move s' ma.m)).A_wins,
  { convert A_wins_at_play_move_of h₁,
    rw init_game_play_move hs, change _ = dite _ _ _,
    have h₃ : (play_D_move_at (init_game a d s) hs).s = s',
    { change apply_D_move s _ = apply_D_move s _,
      congr, change dite _ _ _ = md, change (init_game a d s).s with s,
      rw dif_pos rfl },
    simp_rw h₃, rw dif_pos, swap, { split; assumption },
    ext; try {refl}, rw play_A_move_at', dsimp,

    -- DAMN DEPENDENT TYPES!

    sorry
    -- simp_rw h₃, change (play_D_move_at (init_game a d s) hs).a with a,
    -- generalize_proofs h₄, convert_to _ = apply_A_move s' (a.f s' hs h₂).m,
    -- { congr; try {exact h₃}, convert_to trivial == trivial,
    --   { exact eq_true_intro h₄ }, { exact eq_true_intro h₂ }, refl
  },
  let g : Game pw := _, change g.A_wins at h₃,
  let g₁ : Game pw := _, change g₁.A_wins,
  have h₄ : g₁ = g.set_D (d.set_move s md₀) := rfl, rw h₄, clear h₄,
  have h₄ : s.len < (g.set_D d).s.len,
  { exact length_lt_length_snoc₂ },
  apply (D_set_move_A_wins_iff h₄).mpr, exact h₃,
end

def mk_D_st_for_ma_exi_D_st {pw : ℕ} {s' : State}
  (h : ∀ (ma : Valid_A_move pw s'.board),
    ∃ (d : D), ∀ (a : A pw),
    (init_game a d (apply_A_move s' ma.m)).D_wins) :
  D :=
begin
  refine ⟨λ sx, _⟩,
  apply dite (∃ (ma : Valid_A_move pw s'.board),
    A_played_move_at sx s' ma); rintro h₁,
  { exact (h h₁.some).some.f sx },
  { exact default },
end

-- Lemma 3.1.1
-- Ross Bryant - Borel determinacy and metamathematics
-- Master's thesis, University of North Texas, 2001
lemma exi_A_move_hws_of_not_D_hws {pw : ℕ} {s : State}
  (h : ¬D_hws_at pw s) :
  ∀ (md : Valid_D_move s.board),
  ∃ (ma : Valid_A_move pw (apply_D_move s md.m).board),
  ¬D_hws_at pw (apply_A_move (apply_D_move s md.m) ma.m) :=
begin
  have hs := act_of_not_D_hws h,
  have h₁ := exi_moves_hws_of_not_D_hws h,
  intro md, specialize h₁ md, simp_rw D_hws_at, contrapose! h₁,
  simp_rw not_A_wins_at at h₁ ⊢,
  let D := mk_D_st_for_ma_exi_D_st h₁, use D,
  rintro ma a, have h₂ := h₁ ma, let s' := apply_D_move s md.m,
  change apply_D_move s md.m with s' at ma h₁ h₂ ⊢,
  let s₁ := apply_A_move s' ma.m,
  change apply_A_move s' ma.m with s₁ at h₁ h₂ ⊢,
  let d := h₂.some, have h₃ := h₂.some_spec,
  change ∀ (a : A pw), (init_game a d s₁).D_wins at h₃,
  specialize h₃ a, contrapose! h₃, rw not_D_wins_at at h₃ ⊢,
  intro n, specialize h₃ n, suffices h₄ : (init_game a D s₁).play n =
    ((init_game a d s₁).play n).set_D D, { rwa h₄ at h₃ }, clear h₃,
  induction n with n ih, { refl }, simp_rw [play_at_succ', ih], clear ih,
  let g : Game pw := _, change (init_game a d s₁).play n with g,
  simp_rw Game.play_move, change (g.set_D D).act with g.act,
  split_ifs with h₃, swap, { refl }, have h₅ : g.d = d := play_at_players_eq.2,
  simp_rw play_D_move_at, change (g.set_D D).s with g.s,
  change (g.set_D D).d with D, rw h₅,
  suffices h₆ : apply_D_move g.s (D.f g.s h₃).m =
    apply_D_move g.s (d.f g.s h₃).m,
  { rw [h₆, ←play_A_move_at_set_D], refl },
  simp_rw apply_D_move, congr' 3,
  have h₆ : ∃ (ma : Valid_A_move pw s'.board),
    A_played_move_at g.s s' ma,
  { exact ⟨_, A_played_move_at_play
    (A_played_move_at_apply_move hs rfl)⟩ },
  change (mk_D_st_for_ma_exi_D_st _).f _ _ = _,
  rw mk_D_st_for_ma_exi_D_st, dsimp,
  split_ifs with hx, swap, { contradiction }, clear hx,
  generalize_proofs h₇, change apply_D_move s md.m with s' at h₇,
  have h₈ := h₇.some_spec, change d with h₂.some, congr,
  suffices h₉ : apply_A_move (apply_D_move s md.m) h₆.some.m = s₁,
  { rw h₉ }, change apply_A_move s' _ = apply_A_move _ _, congr,
  apply A_played_move_at_eq h₆.some_spec,
  exact A_played_move_at_play (A_played_move_at_apply_move hs rfl),
end

def mk_A_st_for_not_D_hws (pw : ℕ) : A pw :=
begin
  refine ⟨λ s' h, _⟩,
  apply dite (∃ (s : State) (md : Valid_D_move s.board),
    ¬D_hws_at pw s ∧ s' = apply_D_move s md.m); rintro h₁ h₂,
  { refine (_ : ∃ (ma : Valid_A_move pw s'.board),
      ¬D_hws_at pw (apply_A_move s' ma.m)).some,
    rcases h₁ with ⟨s, md, h₁, rfl⟩,
    use (exi_A_move_hws_of_not_D_hws h₁ _).some,
    generalize_proofs h₂, exact h₂.some_spec },
  { exact ⟨_, h₂.some_spec⟩ },
end

lemma not_D_hws_at_play_of_not_D_hws {pw n : ℕ} {g : Game pw}
  (h₁ : g.a = mk_A_st_for_not_D_hws pw)
  (h₂ : ¬D_hws_at pw g.s) :
  ¬D_hws_at pw (g.play n).s :=
begin
  rename g g₀, induction n with n ih, { exact h₂ }, clear h₂,
  rw play_at_succ', let g : Game pw := _,
  change ¬D_hws_at pw g.s at ih,
  change ¬D_hws_at pw g.play_move.s,
  change g.play_move with dite _ _ _,
  split_ifs, swap, { exact ih },
  let d := g.d, let s := g.s, let md := d.f s h,
  let s' := apply_D_move s md.m,
  have h₃ : ∃ (ma : Valid_A_move pw s'.board),
    ¬D_hws_at pw (apply_A_move s' ma.m),
  { exact exi_A_move_hws_of_not_D_hws ih md },
  have ma := h₃.some, have h₄ := h₃.some_spec,
  convert h₄, change Game.s (dite _ _ _) = _,
  have h₅ : A_has_valid_move pw s'.board := ⟨_, ma.h⟩,
  change (play_D_move_at g h).s with s',
  rw dif_pos, swap, { split; assumption },
  change apply_A_move _ _ = _, congr,
  change g.a.f s' h h₅ = _, let A : A pw := _, change g₀.a = A at h₁,
  have h₆ : g.a = A := by { rw ←h₁, exact play_at_players_eq.1 },
  rw h₆, change (mk_A_st_for_not_D_hws pw).f _ _ _ = _,
  rw mk_A_st_for_not_D_hws, dsimp, rw dif_pos, exact ⟨s, md, ih, rfl⟩,
end

lemma A_hws_at_of {pw : ℕ} {s : State}
  (h : ¬D_hws_at pw s) : A_hws_at pw s :=
begin
  have hs : s.act := act_of_not_D_hws h,
  let A := mk_A_st_for_not_D_hws pw, use A, rintro d n,
  induction n with n ih, { exact hs }, rw play_at_succ',
  let g : Game pw := _, change g.act at ih, change g.play_move.act,
  let s := g.s, let md := d.f s ih, let s' := apply_D_move s md.m,
  rw play_move_at_act ih, have h₁ : play_D_move_at g ih = g.set_state s',
  { convert play_D_move_eq, change apply_D_move _ (d.f s ih).m = _,
    congr, symmetry, exact play_at_players_eq.2 },
  rw h₁, clear h₁, have h₁ : A_has_valid_move pw s'.board,
  { have h₁ : ¬D_hws_at pw s := not_D_hws_at_play_of_not_D_hws rfl h,
    exact ⟨_, (exi_A_move_hws_of_not_D_hws h₁ md).some.h⟩ },
  change Game.act (dite _ _ _), change (g.set_state s').s with s',
  rw dif_pos, swap, { split; assumption }, exact ih,
end

-----

lemma D_hws_at_of {pw : ℕ} {s : State}
  (h : ¬A_hws_at pw s) : D_hws_at pw s :=
by { contrapose! h, exact A_hws_at_of h }

lemma not_A_hws_at_iff {pw : ℕ} {s : State} :
  ¬A_hws_at pw s ↔ D_hws_at pw s :=
⟨D_hws_at_of, not_A_hws_at_of⟩

lemma not_D_hws_at_iff {pw : ℕ} {s : State} :
  ¬D_hws_at pw s ↔ A_hws_at pw s :=
⟨A_hws_at_of, not_D_hws_at_of⟩