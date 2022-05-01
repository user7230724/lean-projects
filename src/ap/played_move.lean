import tactic
import tactic.induction
import data.int.basic
import data.set.basic
import logic.function.iterate
import data.list

import .base .game

noncomputable theory
open_locale classical

def A_played_move_at {pw : ℕ} (s : State) (s₀' : State)
  (ma : Valid_A_move pw s₀'.board) : Prop :=
∃ (s₀ : State) (md : Valid_D_move s₀.board) (a : A pw) (d : D) (n : ℕ),
(∃ hs, d.f s₀ hs = md) ∧
s₀' = apply_D_move s₀ md.m ∧
(∃ hs h, a.f s₀' hs h = ma) ∧
n ≠ 0 ∧
s = ((init_game a d s₀).play n).s

-----

lemma A_played_move_at_apply_move {pw : ℕ} {s s' : State}
  {md : Valid_D_move s.board} {ma : Valid_A_move pw s'.board}
  (hs : s.act) (h : s' = apply_D_move s md.m) :
  A_played_move_at (apply_A_move s' ma.m) s' ma :=
begin
  let a := (default : A pw).set_move s' ma,
  let d := (default : D).set_move s md,
  use [s, md, a, d, 1, ⟨hs, D_set_move_eq_pos⟩, h],
  have hs₁ : s'.act := by rwa h,
  have hvm_s' : A_has_valid_move pw s'.board := ⟨_, ma.h⟩,
  refine ⟨_, _, _⟩, { exact ⟨hs₁, hvm_s', A_set_move_eq_pos⟩ },
  { dec_trivial }, rw [play_1, play_move_at_act], swap, { exact hs },
  rw play_A_move_at, rw dif_pos, swap,
  { use hs, convert hvm_s', convert h.symm,
    change apply_D_move s (d.f s hs).m = _, congr,
    exact D_set_move_eq_pos },
  symmetry, change apply_A_move _ _ = _,
  have h₁ : (play_D_move_at (init_game a d s) hs).s = s',
  { convert h.symm, change apply_D_move s (d.f s hs).m = _,
    congr, exact D_set_move_eq_pos },
  congr' 1, change (a.f _ _ _).m = _, generalize_proofs h₂,
  have h₃ : (a.f (play_D_move_at (init_game a d s) hs).s hs h₂).m =
    (a.f s' hs₁ hvm_s').m, { congr' },
  rw [h₃, A_set_move_eq_pos],
end

lemma A_hvm_of_next_act {pw : ℕ} {g : Game pw}
  (h : g.play_move.act) :
  ∃ hs, A_has_valid_move pw (play_D_move_at g hs).s.board :=
begin
  have hs : g.act := act_of_act_play_move h, use hs,
  rw Game.play_move at h, rw dif_pos hs at h,
  rw play_A_move_at at h, split_ifs at h with h₄,
  { cases h₄ with h₄ h₅, convert h₅, },
  { cases h }
end

lemma play_move_hist_len_eq_of_act {pw : ℕ} {g : Game pw}
  (h : g.play_move.act) :
  g.play_move.s.len = g.s.len + 2 :=
begin
  have h₁ : g.act := act_of_act_play_move h,
  rw [play_move_at_act h₁, play_A_move_at],
  rw dif_pos, { rw [hist_len_play_A_move_at', hist_len_play_D_move_at] },
  exact ⟨h₁, (A_hvm_of_next_act h).some_spec⟩,
end

lemma play_hist_len_eq_of_act {pw n : ℕ} {g : Game pw}
  (h : (g.play n).act) :
  (g.play n).s.len = g.s.len + n * 2 :=
begin
  induction n with n ih, { refl }, rw play_at_succ' at h ⊢,
  let g₁ : Game pw := _, change g.play n with g₁ at ih h ⊢,
  have h₁ := act_of_act_play_move h, specialize ih h₁,
  rw [play_move_hist_len_eq_of_act h, ih, add_assoc, nat.succ_mul],
end

lemma hist_len_ne_of_play_lt {pw n k : ℕ} {g : Game pw}
  (h₁ : k < n) (h₂ : (g.play n).act) :
  (g.play k).s.len ≠ (g.play n).s.len :=
begin
  have h₃ := act_play_le (nat.le_of_lt h₁) h₂,
  rw [play_hist_len_eq_of_act h₂, play_hist_len_eq_of_act h₃], intro h,
  replace h := nat.add_left_cancel h,
  rw nat.mul_left_inj at h, swap, { dec_trivial },
  subst h, exact nat.lt_asymm h₁ h₁,
end

lemma hist_ne_of_play_lt {pw n k : ℕ} {g : Game pw}
  (h₁ : k < n) (h₂ : (g.play n).act) :
  (g.play k).s.history ≠ (g.play n).s.history :=
hist_ne_of_hist_len_ne (hist_len_ne_of_play_lt h₁ h₂)

lemma state_ne_of_play_lt {pw n k : ℕ} {g : Game pw}
  (h₁ : k < n) (h₂ : (g.play n).act) :
  (g.play k).s ≠ (g.play n).s :=
by { have h₃ := hist_ne_of_play_lt h₁ h₂, contrapose! h₃, rw h₃ }

lemma apply_A_move_ne_of_hist_ne {pw : ℕ} {s₁ s₂ : State}
  {ma₁ ma₂ : A_move} (h : s₁.len ≠ s₂.len) :
  apply_A_move s₁ ma₁ ≠ apply_A_move s₂ ma₂ :=
begin
  contrapose! h, simp_rw [apply_A_move, apply_move] at h,
  simp_rw [State.len, (snoc_eq_snoc_iff.mp h.2.1).1],
end

lemma apply_D_move_ne_of_hist_ne {s₁ s₂ : State}
  {md₁ md₂ : D_move} (h : s₁.len ≠ s₂.len) :
  apply_D_move s₁ md₁ ≠ apply_D_move s₂ md₂ :=
begin
  contrapose! h, simp_rw [apply_D_move, apply_move] at h,
  simp_rw [State.len, (snoc_eq_snoc_iff.mp h.2.1).1],
end

def mk_A_for_played_move_at_play_move {pw : ℕ}
  (a₀ a : A pw) (s' : State) (hs : s'.act) :
  A pw :=
if hvm : A_has_valid_move pw s'.board
then a₀.set_move s' (a.f s' hs hvm)
else a₀

lemma A_played_move_at_play_move {pw : ℕ}
  {g : Game pw} {s₀' : State} {ma : Valid_A_move pw s₀'.board}
  (h : A_played_move_at g.s s₀' ma) :
  A_played_move_at g.play_move.s s₀' ma :=
begin
  let a := g.a, let d := g.d, let s := g.s,
  rcases h with ⟨s₀, md₀, a₀, d₀, n, hmd, h₁, hx, hy, h₂⟩, by_cases hs : g.act,
  { let md := d.f s hs, let s' := apply_D_move s md.m,
    let d₁ := d₀.set_move s md,
    let a₁ := mk_A_for_played_move_at_play_move a₀ a s' hs,
    have hmd₁ : ∃ hs, d₁.f s₀ hs = md₀,
    { cases hmd with hs₁ hmd, use hs₁, change dite _ _ _ = _,
      rw dif_neg, { exact hmd }, change ((init_game a₀ d₀ s₀).play 0).s ≠ g.s,
      rw h₂, apply state_ne_of_play_lt (nat.pos_of_ne_zero hy),
      change g.s.act at hs, rwa h₂ at hs },
    use [s₀, md₀, a₁, d₁, n.succ, hmd₁, by rw h₁],
    have h₁ : ∀ (k ≤ n), ((init_game a₁ d₁ s₀).play k).s =
      ((init_game a₀ d₀ s₀).play k).s,
    { rintro k hk, induction k with k ih, { refl }, simp_rw play_at_succ',
      specialize ih (nat.le_of_succ_le hk),
      replace ih : (init_game a₁ d₁ s₀).play k =
        ((init_game a₀ d₀ s₀).play k).set_players a₁ d₁,
      { ext,
        { exact play_at_players_eq.1 },
        { exact play_at_players_eq.2 },
        { rw ih, refl }},
      rw ih, clear ih,
      have hs₁ : ((init_game a₀ d₀ s₀).play k).act,
      { apply act_play_le (nat.le_of_succ_le hk),
        change ((init_game a₀ d₀ s₀).play n).s.act,
        rw ←h₂, exact hs },
      repeat { rw play_move_at_act, swap, { exact hs₁ }},
      let g₁ : Game pw := _,
      change (init_game a₀ d₀ s₀).play k with g₁ at hs₁ ⊢,
      have ha : g₁.a = a₀ := play_at_players_eq.1,
      have hd : g₁.d = d₀ := play_at_players_eq.2,
      let sk := g₁.s, let mdk := d₀.f sk hs₁,
      let sk' := apply_D_move sk mdk.m,
      have hy : (play_D_move_at g₁ hs₁).s = sk',
      { change apply_D_move sk _ = apply_D_move _ _, congr' 2, rw hd },
      have h₁ : d₁.f sk hs₁ = mdk,
      { change dite _ _ _ = _, rw dif_neg,
        change ((init_game a₀ d₀ s₀).play k).s ≠ g.s, rw h₂,
        apply state_ne_of_play_lt (nat.succ_le_iff.mp hk),
        change ((init_game a₀ d₀ s₀).play n).s.act, rw ←h₂, exact hs },
      have hx : play_D_move_at (g₁.set_players a₁ d₁) hs₁ =
        (play_D_move_at g₁ hs₁).set_players a₁ d₁,
      { ext,
        { exact play_D_move_at_players_eq.1, },
        { exact play_D_move_at_players_eq.2, },
        { change apply_D_move g₁.s _ = apply_D_move _ _,
          congr' 2, change d₁.f sk _ = _, rw [h₁, hd] }},
      rw hx, clear hx, have hx : A_has_valid_move pw sk'.board,
      { have h₃ : g₁.play_move.act,
        { change ((init_game a₀ d₀ s₀).play k).play_move.act,
          rw ←play_at_succ', apply act_play_le hk,
          change ((init_game a₀ d₀ s₀).play n).s.act,
          rw ←h₂, exact hs },
        convert (A_hvm_of_next_act h₃).some_spec, rw ←hy, refl },
      simp_rw play_A_move_at,
      repeat { rw dif_pos, swap, { use hs₁, convert hx }},
      change apply_A_move (play_D_move_at g₁ hs₁).s
        (a₁.f (play_D_move_at g₁ hs₁).s _ _).m =
        apply_A_move _ (g₁.a.f (play_D_move_at g₁ hs₁).s _ _).m,
      congr' 2, rw ha, generalize_proofs h₃,
      change (mk_A_for_played_move_at_play_move _ _ _ _).f _ _ _ = _,
      rw mk_A_for_played_move_at_play_move,
      split_ifs with hh, swap, { refl },
      change dite _ _ _ = _, rw dif_neg, rw hy,
      change apply_D_move ((init_game a₀ d₀ s₀).play k).s mdk.m ≠
        apply_D_move g.s md.m,
      rw h₂, replace hk := nat.lt_of_succ_le hk,
      apply apply_D_move_ne_of_hist_ne, apply hist_len_ne_of_play_lt hk,
      change ((init_game a₀ d₀ s₀).play n).s.act, rw ←h₂, exact hs },
    specialize h₁ n (le_refl n),
    replace h₁ : (init_game a₁ d₁ s₀).play n = g.set_players a₁ d₁,
    { ext,
      { exact play_at_players_eq.1 },
      { exact play_at_players_eq.2 },
      { rw h₁, exact h₂.symm }},
    rw [play_at_succ', play_move_at_act hs, h₁, play_move_at_act],
    swap, { exact hs }, refine ⟨_, _, _⟩,
    { clear h₁, rcases hx with ⟨hs', h, hx⟩,
      use [hs', h], rw ←hx, clear hx,
      change (mk_A_for_played_move_at_play_move _ _ _ _).f _ _ _ = _,
      rw mk_A_for_played_move_at_play_move,
      split_ifs with hss, swap, { refl }, change dite _ _ _ = _,
      rw dif_neg, change s₀' ≠ apply_D_move g.s _, rw [h₁, h₂],
      apply apply_D_move_ne_of_hist_ne,
      change ((init_game a₀ d₀ s₀).play 0).s.len ≠ _,
      apply hist_len_ne_of_play_lt (pos_iff_ne_zero.mpr hy),
      rw [Game.act, ←h₂], exact hs }, { dec_trivial }, symmetry,
    have h₁ : play_D_move_at (g.set_players a₁ d₁) hs =
      (play_D_move_at g hs).set_players a₁ d₁,
    { ext,
      { exact play_D_move_at_players_eq.1 },
      { exact play_D_move_at_players_eq.2 },
      { change apply_D_move g.s _ = apply_D_move _ _,
        congr' 2, change d₁.f s hs = g.d.f g.s hs,
        change dite _ _ _ = _, rw dif_pos rfl }},
    rw h₁, clear h₁, simp_rw play_A_move_at,
    split_ifs with h₁, swap, { refl }, cases h₁ with h₁ h₂,
    change apply_A_move ((play_D_move_at g hs).s) _ =
      apply_A_move _ _,
    congr' 2, change a₁.f s' _ _ = a.f s' _ _, generalize_proofs,
    change (mk_A_for_played_move_at_play_move _ _ _ _).f _ _ _ = _,
    rw mk_A_for_played_move_at_play_move, rw dif_pos, swap, { exact h₂ },
    change dite _ _ _ = _, rw dif_pos rfl },
  { use [s₀, md₀, a₀, d₀, n, hmd, h₁, hx, hy],
    rw play_move_at_not_act hs, exact h₂ },
end

lemma A_played_move_at_play {pw n : ℕ}
  {g : Game pw} {s' : State} {ma : Valid_A_move pw s'.board}
  (h : A_played_move_at g.s s' ma) :
  A_played_move_at (g.play n).s s' ma :=
begin
  induction n with n ih, { exact h }, rw play_at_succ',
  exact A_played_move_at_play_move ih,
end

lemma hist_overlaps_of_A_played_move_at {pw : ℕ}
  {s s₀' : State} {ma : Valid_A_move pw s₀'.board}
  (h₁ : A_played_move_at s s₀' ma) :
  ∀ (k : ℕ), k.succ < s₀'.len →
  s.history.nth k = s₀'.history.nth k :=
begin
  rintro k h₂,
  rcases h₁ with ⟨s₀, md, a, d, n, hmd, rfl, hx, hy, rfl⟩, clear' hx hy,
  change (apply_D_move s₀ md.m).history with (_ ++ _ : list _) at h₂ ⊢,
  change _ < (snoc _ _).length at h₂,
  rw [length_snoc, nat.succ_lt_succ_iff] at h₂ ,induction n with n ih,
  { change s₀.history.nth k = _, exact (list.nth_append h₂).symm },
  { simp_rw play_at_succ', let g : Game pw := _,
    change (init_game a d s₀).play n with g at h₂ ih ⊢, rw ←ih, clear ih,
    rw Game.play_move, split_ifs with hs, swap, { refl }, rw play_A_move_at,
    have h₆ : s₀.len ≤ g.s.len,
    { change (init_game a d s₀).s.len ≤ _, exact hist_len_le_play },
    split_ifs with h₃,
    { change (_ ++ _ : list _).nth _ = _, rw list.nth_append,
      { change (_ ++ _ : list _).nth _ = _, rw list.nth_append,
        exact gt_of_ge_of_gt h₆ h₂ },
      { rw [←State.len, hist_len_play_D_move_at],
        exact nat.lt_succ_of_le (nat.le_trans (le_of_lt h₂) h₆) }},
    { change (_ ++ _ : list _).nth _ = _, rw list.nth_append,
      exact gt_of_ge_of_gt h₆ h₂ }},
end

lemma A_played_move_at_eq_aux {pw n : ℕ}
  {sx s₀ s' : State} {md : Valid_D_move s₀.board}
  {a : A pw} {d : D} {hs hvm h₄}
  (h₁ : s' = apply_D_move s₀ md.m)
  (h₂ : sx = ((init_game a d s₀).play n).s)
  (h₃ : n ≠ 0)
  (hh : md = d.f s₀ h₄) :
  sx.nth (s₀.len + 2) = option.some
    (apply_A_move s' (a.f s' hs hvm).m).board :=
begin
  cases n, { contradiction }, clear h₃,
  let i : ℕ := _, change s₀.len + 2 with i,
  let s₁ : State := apply_A_move s' (a.f s' hs hvm).m,
  change _ = some (State.board s₁), have h₅ : i = s₁.len,
  { change s₁ with apply_A_move _ _, subst s',
    rw [apply_A_move_len, apply_D_move_len] },
  induction n with n ih generalizing sx,
  { rw [play_1, play_move_at_act] at h₂, swap, { exact h₄ },
    subst sx, have h₆ : play_D_move_at (init_game a d s₀) h₄ =
      (init_game a d s'),
    { ext,
      { exact play_D_move_at_players_eq.1 },
      { exact play_D_move_at_players_eq.2 },
      { subst s',
        change apply_D_move s₀ (d.f s₀ _).m = apply_D_move s₀ _, rw hh }},
    rw [h₆, play_A_move_at, dif_pos], clear h₆, swap, { exact ⟨hs, hvm⟩ },
    change s₁.nth _ = _, rw h₅, exact state_nth_len },
  { rw play_at_succ' at h₂, let g₁ : Game pw := (init_game a d s₀).play n.succ,
    change (init_game a d s₀).play n.succ with g₁ at ih h₂, subst sx,
    specialize ih rfl, rw Game.play_move, split_ifs with hs₁, swap, { exact ih },
    let g₂ : Game pw := _, change play_D_move_at g₁ hs₁ with g₂,
    have ih₁ : g₂.s.nth i = some s₁.board,
    { exact apply_move_state_nth_eq_some_of ih },
    rw play_A_move_at, split_ifs with hh,
    { exact apply_move_state_nth_eq_some_of ih₁ },
    { exact ih₁ }},
end

lemma A_played_move_at_eq {pw : ℕ}
  {sx s' : State} {ma₁ ma₂ : Valid_A_move pw s'.board}
  (hx : A_played_move_at sx s' ma₁)
  (hy : A_played_move_at sx s' ma₂) :
  ma₁ = ma₂ :=
begin
  obtain ⟨s₀, md₁, a₁, d₁, n₁, hmd₁, h₁, ⟨hs₁, hvm₁, rfl⟩, h₃, h₄⟩ := hx,
  obtain ⟨s₀', md₂, a₂, d₂, n₂, hmd₂, h₅, ⟨hs₂, hvm₂, rfl⟩, h₇, h₈⟩ := hy,
  have hs : s₀.act,
  { subst s', exact hs₂ },
  obtain rfl : s₀ = s₀',
  { subst h₁, exact state_eq_of_apply_D_move_eq h₅ },
  obtain rfl : md₁ = md₂,
  { subst h₁, rwa ←D_moves_eq_iff at h₅ },
  clear h₅, change hvm₂ with hvm₁, clear hvm₂,
  change hs₂ with hs₁, clear hs₂, let i := s₀.len,
  have h₅ : sx.nth (i + 2) = option.some
    (apply_A_move s' (a₁.f s' hs₁ hvm₁).m).board,
  { exact A_played_move_at_eq_aux h₁ h₄ h₃ hmd₁.some_spec.symm },
  have h₆ : sx.nth (i + 2) = option.some
    (apply_A_move s' (a₂.f s' hs₁ hvm₁).m).board,
  { exact A_played_move_at_eq_aux h₁ h₈ h₇ hmd₂.some_spec.symm },
  simp [h₅] at h₆, rwa A_moves_eq_iff',
end