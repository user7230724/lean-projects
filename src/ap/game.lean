import tactic
import tactic.induction
import data.int.basic
import data.set.basic
import logic.function.iterate
import data.list

import .base .point .dist .board .state .player

noncomputable theory
open_locale classical

def Game.set_A {pw pw₁ : ℕ} (g : Game pw) (a₁ : A pw₁) : Game pw₁ :=
{g with a := a₁}

def Game.set_D {pw : ℕ} (g : Game pw) (d₁ : D) : Game pw :=
{g with d := d₁}

def Game.set_players {pw pw₁ : ℕ} (g : Game pw)
  (a₁ : A pw₁) (d₁ : D) : Game pw₁ :=
(g.set_A a₁).set_D d₁

def Game.set_prev_moves {pw : ℕ} (g : Game pw)
  (fa : A_prev_moves pw g.s)
  (fd : D_prev_moves g.s) : Game pw :=
g.set_players (g.a.set_prev_moves g.s fa) (g.d.set_prev_moves g.s fd)

def Game.D_wins {pw : ℕ} (g : Game pw) :=
∃ (n : ℕ), ¬(g.play n).act

def D_hws_at (pw : ℕ) (s : State) :=
∃ (d : D), ∀ (a : A pw), (init_game a d s).D_wins

def D_hws (pw : ℕ) := D_hws_at pw state₀

-----

lemma not_A_wins_at {pw : ℕ} {g : Game pw} :
  ¬g.A_wins ↔ g.D_wins :=
by simp [Game.A_wins, Game.D_wins]

lemma not_D_wins_at {pw : ℕ} {g : Game pw} :
  ¬g.D_wins ↔ g.A_wins :=
by simp [Game.A_wins, Game.D_wins]

lemma play_at_succ {pw n : ℕ} {g : Game pw} :
  g.play n.succ = g.play_move.play n :=
function.iterate_succ_apply _ _ _

lemma play_at_succ' {pw n : ℕ} {g : Game pw} :
  g.play n.succ = (g.play n).play_move :=
function.iterate_succ_apply' _ _ _

-----

lemma A_wins_at_play_of {pw : ℕ} {g : Game pw}
  (h : g.A_wins) {n : ℕ} : (g.play n).A_wins :=
begin
  intro k, specialize h (k + n),
  rw [Game.play, function.iterate_add] at h, exact h,
end

lemma A_wins_at_play_move_of {pw : ℕ} {g : Game pw}
  (h : g.A_wins) : g.play_move.A_wins :=
@A_wins_at_play_of _ _ h 1

lemma play_A_move_at_players_eq {pw : ℕ} {g : Game pw} :
  (play_A_move_at g).a = g.a ∧ (play_A_move_at g).d = g.d :=
by { rw [play_A_move_at], split_ifs; exact ⟨rfl, rfl⟩ }

lemma play_D_move_at_players_eq {pw : ℕ} {g : Game pw} {hs} :
  (play_D_move_at g hs).a = g.a ∧ (play_D_move_at g hs).d = g.d :=
by { rw [play_D_move_at], exact ⟨rfl, rfl⟩ }

lemma play_move_at_players_eq {pw : ℕ} {g : Game pw} :
  g.play_move.a = g.a ∧ g.play_move.d = g.d :=
begin
  rw [Game.play_move], split_ifs, swap, exact ⟨rfl, rfl⟩,
  rw [play_A_move_at_players_eq.1, play_A_move_at_players_eq.2],
  rw [play_D_move_at_players_eq.1, play_D_move_at_players_eq.2],
  exact ⟨rfl, rfl⟩,
end

lemma play_move_at_players_eq' {pw : ℕ} {g : Game pw} {hs} :
  (play_A_move_at (play_D_move_at g hs)).a = g.a ∧
  (play_A_move_at (play_D_move_at g hs)).d = g.d :=
by { rw play_A_move_at, split_ifs; exact ⟨rfl, rfl⟩ }

lemma play_at_players_eq {pw n : ℕ} {g : Game pw} :
  (g.play n).a = g.a ∧ (g.play n).d = g.d :=
begin
  induction n with n ih,
  { exact ⟨rfl, rfl⟩ },
  { simp_rw play_at_succ',
    rwa [play_move_at_players_eq.1, play_move_at_players_eq.2] },
end

lemma play_move_at_act {pw : ℕ} {g : Game pw}
  (h : g.act) :
  g.play_move = play_A_move_at (play_D_move_at g h) :=
dif_pos h

lemma play_move_at_not_act {pw : ℕ} {g : Game pw}
  (h : ¬g.act) :
  g.play_move = g :=
dif_neg h

lemma play_A_move_hvm {pw : ℕ} {g : Game pw} (hs)
  (h : A_has_valid_move pw g.s.board) :
  ∃ h, play_A_move_at g = play_A_move_at' g.a g hs h :=
by exact ⟨_, dif_pos ⟨hs, h⟩⟩

lemma play_A_move_at_set_D {pw : ℕ}
  {g : Game pw} {d₁ : D} :
  play_A_move_at (g.set_D d₁) = (play_A_move_at g).set_D d₁ :=
by { simp_rw play_A_move_at, split_ifs; refl }

lemma play_D_move_at_set_A {pw pw₁ : ℕ}
  {g : Game pw} {a₁ : A pw₁} {hs} :
  play_D_move_at (g.set_A a₁) hs =
  (play_D_move_at g hs).set_A a₁ :=
rfl

lemma A_has_valid_move_at_play_D_move {pw : ℕ} {g : Game pw} {hs}
  (h : g.A_wins) :
  A_has_valid_move pw (play_D_move_at g hs).s.board :=
begin
  specialize h 1, change g.play_move.act at h,
  rw play_move_at_act hs at h, rw play_A_move_at at h,
  split_ifs at h with h₁,
  { exact h₁.2 },
  { cases h },
end

-----

lemma act_of_act_play_move {pw : ℕ} {g : Game pw}
  (h : g.play_move.act) : g.act :=
by { rw Game.play_move at h, split_ifs at h with h₁; assumption }

lemma act_play_of_act_play_succ {pw n : ℕ} {g : Game pw}
  (h : (g.play n.succ).act) : (g.play n).act :=
by { rw play_at_succ' at h, exact act_of_act_play_move h }

lemma act_play_le {pw n m : ℕ} {g : Game pw}
  (h₁ : n ≤ m) (h₂ : (g.play m).act) : (g.play n).act :=
begin
  induction' h₁,
  { exact h₂ },
  { rw play_at_succ' at h₂, exact ih (act_of_act_play_move h₂) },
end

lemma hist_len_play_A_move_at' {pw pw₁ : ℕ} {g : Game pw}
  {a₁ : A pw₁} {h₁ h₂} :
  (play_A_move_at' a₁ g h₁ h₂).s.len = g.s.len.succ :=
hist_len_apply_A_move

lemma hist_len_play_D_move_at {pw : ℕ} {g : Game pw} {hs} :
  (play_D_move_at g hs).s.len = g.s.len.succ :=
hist_len_apply_D_move

lemma play_A_move_at_hist_len_ge {pw : ℕ} {g : Game pw} :
  g.s.len ≤ (play_A_move_at g).s.len :=
begin
  rw play_A_move_at, split_ifs, swap, { refl },
  rw hist_len_play_A_move_at',
  exact nat.le_of_lt (nat.lt_succ_self _),
end

lemma play_D_move_at_hist_len_ge {pw : ℕ} {g : Game pw} {hs} :
  g.s.len ≤ (play_D_move_at g hs).s.len :=
by { rw hist_len_play_D_move_at, exact nat.le_of_lt (nat.lt_succ_self _) }

lemma play_D_move_at_hist_len_eq {pw : ℕ} {g : Game pw} {hs} :
  (play_D_move_at g hs).s.len = g.s.len.succ :=
by rw hist_len_play_D_move_at

lemma play_move_at_hist_len_ge {pw : ℕ} {g : Game pw} :
  g.s.len ≤ g.play_move.s.len :=
begin
  rw Game.play_move, split_ifs with hs, swap, { refl },
  rw play_A_move_at, split_ifs with h₁,
  { change (play_D_move_at g hs).a with g.a,
    transitivity (play_D_move_at g hs).s.len,
    { exact play_D_move_at_hist_len_ge },
    { rw hist_len_play_A_move_at',
      exact nat.le_of_lt (nat.lt_succ_self _) }},
  { change _ ≤ (play_D_move_at g hs).s.len,
    rw hist_len_play_D_move_at,
    exact nat.le_of_lt (nat.lt_succ_self _) },
end

lemma play_at_hist_len_ge {pw n : ℕ} {g : Game pw} :
  g.s.len ≤ (g.play n).s.len :=
begin
  induction n with n ih,
  { refl },
  { apply le_trans ih, clear ih, rw play_at_succ',
    exact play_move_at_hist_len_ge },
end

lemma set_players_flip {pw pw₁ : ℕ} {g : Game pw}
  {a₁ : A pw₁} {d₁ : D} :
  (g.set_A a₁).set_D d₁ = (g.set_D d₁).set_A a₁ :=
rfl

lemma play_move_eq_set_state_of_act_next {pw : ℕ} {g : Game pw}
  (h : g.play_move.act) :
  g.play_move = g.set_state g.play_move.s :=
begin
  ext,
  { exact play_move_at_players_eq.1 },
  { exact play_move_at_players_eq.2 },
  { refl },
end

lemma play_D_move_eq {pw : ℕ} {g : Game pw} {hs} :
  play_D_move_at g hs =
  g.set_state (apply_D_move g.s (g.d.f g.s hs).m) :=
rfl

-----

lemma set_prev_moves_A_wins_iff {pw : ℕ} {g : Game pw}
  {fa : A_prev_moves pw g.s}
  {fd : D_prev_moves g.s} :
  (g.set_prev_moves fa fd).A_wins ↔ g.A_wins :=
begin
  let a := g.a, let d := g.d,
  let a' := a.set_prev_moves g.s fa,
  let d' := d.set_prev_moves g.s fd,
  let g' : Game pw := _,
  change (∀ n, (g'.play n).act) ↔ (∀ n, ((g.play n).set_players a' d').act),
  suffices h : ∀ {n}, g'.play n = (g.play n).set_players a' d', simp_rw h,
  intro n, induction n with n ih, { refl },
  let g₁ := g.play n,
  let g₁' := g₁.set_players a' d',
  simp_rw play_at_succ', rw ih, clear ih,
  change (g₁.set_players a' d').play_move = g₁.play_move.set_players a' d',
  simp_rw Game.play_move,
  split_ifs, swap, { refl },
  have h₁ : play_D_move_at (g₁.set_players a' d') h =
    (play_D_move_at g₁ h).set_players a' d',
  { simp_rw [Game.set_players, set_players_flip, play_D_move_at_set_A],
    congr, simp_rw play_D_move_at,
    change (g₁.set_D d').d with d',
    ext; try { refl }, change _ = apply_D_move _ _,
    simp [apply_D_move, apply_move], simp_rw Game.set_state,
    refine ⟨_, snoc_eq_snoc_iff.mpr ⟨rfl, rfl⟩, rfl⟩,
    change (g₁.set_D d').s with g₁.s,
    congr' 1, generalize_proofs, change d'.f g₁.s h with dite _ _ _,
    split_ifs with h₂,
    { exfalso, contrapose! h₂, clear h₂,
      transitivity (g.play n).s.len,
      { exact play_at_hist_len_ge },
      { refl }},
    { congr, exact play_at_players_eq.2.symm }},
  rw h₁, clear h₁,
  let g₂ : Game pw := _, change (play_D_move_at g₁ h) with g₂,
  have h₁ : play_A_move_at (g₂.set_A a') =
    (play_A_move_at g₂).set_A a',
  { simp_rw play_A_move_at,
    change dite (g₂.act ∧ A_has_valid_move pw g₂.s.board) _ _ = _,
    split_ifs with hx, swap, { refl },
    change (g₂.set_A a').a with a',
    simp_rw play_A_move_at', ext; try {refl},
    simp_rw Game.set_state,
    change (g₂.set_A a').s with g₂.s at hx ⊢,
    change _ = apply_A_move _ _,
    simp [apply_A_move, apply_move],
    generalize_proofs hy hz,
    change a'.f g₂.s h hy with dite _ _ _,
    split_ifs with h₂,
    { exfalso, contrapose! h₂, clear h₂,
      transitivity (g.play n).s.len,
      { exact play_at_hist_len_ge },
      { exact play_D_move_at_hist_len_ge }},
    { congr, exact play_at_players_eq.1.symm }},
  simp_rw [Game.set_players, play_A_move_at_set_D, h₁],
end

lemma A_set_move_A_wins_iff {pw : ℕ} {g : Game pw}
  {s : State} {m : Valid_A_move pw s.board}
  (h : s.len < g.s.len) :
  (g.set_A (g.a.set_move s m)).A_wins ↔ g.A_wins :=
begin
  convert set_prev_moves_A_wins_iff, ext,
  { change _ = g.a.prev_moves_set g.s s m h, rw A_prev_moves_set_eq, refl },
  repeat { refl }, change _ = g.d.prev_moves_id g.s,
  rw D_prev_moves_id_eq, refl,
end

lemma D_set_move_A_wins_iff {pw : ℕ} {g : Game pw}
  {s : State} {m : Valid_D_move s.board}
  (h : s.len < g.s.len) :
  (g.set_D (g.d.set_move s m)).A_wins ↔ g.A_wins :=
begin
  convert set_prev_moves_A_wins_iff, ext,
  { change _ = g.a.prev_moves_id g.s, rw A_prev_moves_id_eq, },
  repeat { refl }, change _ = g.d.prev_moves_set g.s s m h,
  rw D_prev_moves_set_eq,
end

lemma play_1 {pw : ℕ} {g : Game pw} : g.play 1 = g.play_move := rfl

-----

lemma init_game_act {pw : ℕ}
  {a : A pw} {d : D} {s : State}
  (h : s.act) :
  (init_game a d s).act := h

lemma init_game_play_move {pw : ℕ}
  {a : A pw} {d : D} {s : State} (hs) :
  (init_game a d s).play_move =
  play_A_move_at (play_D_move_at (init_game a d s) hs) :=
dif_pos (init_game_act hs)

lemma hist_len_game_finish {pw : ℕ} {g : Game pw} :
  g.finish.s.len = g.s.len := rfl

lemma hist_len_le_play_move {pw : ℕ} {g : Game pw} :
  g.s.len ≤ g.play_move.s.len :=
begin
  rw Game.play_move, split_ifs with hs, swap, { refl },
  rw play_A_move_at, split_ifs with h,
  { rw [hist_len_play_A_move_at', hist_len_play_D_move_at],
    apply nat.le_succ_of_le (nat.le_succ _) },
  { rw [hist_len_game_finish, hist_len_play_D_move_at],
    apply nat.le_succ },
end

lemma hist_len_le_play {pw n : ℕ} {g : Game pw} :
  g.s.len ≤ (g.play n).s.len :=
begin
  induction n with n ih, { refl }, rw play_at_succ',
  exact ih.trans hist_len_le_play_move,
end

lemma play_add {pw n k} {g : Game pw} :
  g.play (n + k) = (g.play n).play k :=
by { rw add_comm, apply function.iterate_add_apply }

lemma play_add' {pw n k} {g : Game pw} :
  g.play (n + k) = (g.play k).play n :=
by { apply function.iterate_add_apply }

lemma init_game_state_eq {pw : ℕ} {a : A pw} {d : D} {s : State} :
  (init_game a d s).s = s := rfl

lemma play_move_state_eq_of_act_play_move {pw : ℕ} {g : Game pw}
  (h : g.play_move.act) :
  ∃ s' hs hs' hvm, s' = apply_D_move g.s (g.d.f g.s hs).m ∧
  g.play_move.s = apply_A_move s' (g.a.f s' hs' hvm).m :=
begin
  have hs := act_of_act_play_move h,
  let s' := apply_D_move g.s (g.d.f g.s hs).m,
  have hvm : A_has_valid_move pw s'.board,
  { rw [play_move_at_act hs, play_A_move_at] at h,
    split_ifs at h with h₁,
    { exact h₁.2 },
    { cases h }},
  use [s', hs, hs, hvm, rfl],
  rw [play_move_at_act hs, play_A_move_at, dif_pos],
  swap, { exact ⟨hs, hvm⟩ }, refl,
end

lemma act_play_move_of_A_hvm {pw : ℕ} {g : Game pw} {hs}
  (h : A_has_valid_move pw (apply_D_move g.s (g.d.f g.s hs).m).board) :
  g.play_move.act :=
by { rw [play_move_at_act hs, play_A_move_at], split_ifs with h₁; tauto }