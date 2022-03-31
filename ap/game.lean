import tactic.induction
import data.int.basic
import data.set.basic
import logic.function.iterate

import .point .dist .board .state .player

noncomputable theory
open_locale classical

@[ext] structure Game (pw : ℕ) : Type :=
(a : Angel pw)
(d : Devil)
(s : State)

def init_game {pw : ℕ} (a : Angel pw) (d : Devil) (s : State) : Game pw :=
{ a := a, d := d, s := s }

def Game.act {pw : ℕ} (g : Game pw) : Prop :=
g.s.act

def Game.set_angel {pw pw₁ : ℕ} (g : Game pw) (a₁ : Angel pw₁) : Game pw₁ :=
{g with a := a₁}

def Game.set_devil {pw : ℕ} (g : Game pw) (d₁ : Devil) : Game pw :=
{g with d := d₁}

def Game.set_state {pw : ℕ} (g : Game pw) (s₁ : State) : Game pw :=
{g with s := s₁}

def Game.finish {pw : ℕ} (g : Game pw) : Game pw :=
g.set_state g.s.finish

def Game.set_players {pw pw₁ : ℕ} (g : Game pw)
  (a₁ : Angel pw₁) (d₁ : Devil) : Game pw₁ :=
(g.set_angel a₁).set_devil d₁

def Game.set_prev_moves {pw : ℕ} (g : Game pw)
  (fa : Angel_prev_moves pw g.s)
  (fd : Devil_prev_moves g.s) : Game pw :=
g.set_players (g.a.set_prev_moves g.s fa) (g.d.set_prev_moves g.s fd)

def play_angel_move_at' {pw pw₁ : ℕ} (a₁ : Angel pw₁) (g : Game pw) (hs h) :=
g.set_state (apply_angel_move g.s (a₁.f g.s hs h).m)

def play_angel_move_at {pw : ℕ} (g : Game pw) :=
if h : g.act ∧ angel_has_valid_move pw g.s.board
then play_angel_move_at' g.a g h.1 h.2
else g.finish

def play_devil_move_at {pw : ℕ} (g : Game pw) (hs) :=
g.set_state (apply_devil_move g.s (g.d.f g.s hs).m)

def Game.play_move {pw : ℕ} (g : Game pw) :=
if hs : g.act
then play_angel_move_at (play_devil_move_at g hs)
else g

def Game.play {pw : ℕ} (g : Game pw) (n : ℕ) :=
(Game.play_move^[n]) g

def Game.angel_wins {pw : ℕ} (g : Game pw) :=
∀ (n : ℕ), (g.play n).act

def Game.devil_wins {pw : ℕ} (g : Game pw) :=
∃ (n : ℕ), ¬(g.play n).act

def angel_hws_at (pw : ℕ) (s : State) :=
∃ (a : Angel pw), ∀ (d : Devil), (init_game a d s).angel_wins

def devil_hws_at (pw : ℕ) (s : State) :=
∃ (d : Devil), ∀ (a : Angel pw), (init_game a d s).devil_wins

def angel_played_move_at {pw : ℕ} (sx : State) (s' : State)
  (ma : Valid_angel_move pw s'.board) : Prop :=
∃ (s : State) (md : Valid_devil_move s.board) (a : Angel pw) (d : Devil) (n : ℕ),
s' = apply_devil_move s md.m ∧
sx = ((init_game a d s).play n).s

-- #exit

-----

lemma not_angel_wins_at {pw : ℕ} {g : Game pw} :
  ¬g.angel_wins ↔ g.devil_wins :=
by simp [Game.angel_wins, Game.devil_wins]

lemma not_devil_wins_at {pw : ℕ} {g : Game pw} :
  ¬g.devil_wins ↔ g.angel_wins :=
by simp [Game.angel_wins, Game.devil_wins]

lemma play_at_succ {pw n : ℕ} {g : Game pw} :
  g.play n.succ = g.play_move.play n :=
function.iterate_succ_apply _ _ _

lemma play_at_succ' {pw n : ℕ} {g : Game pw} :
  g.play n.succ = (g.play n).play_move :=
function.iterate_succ_apply' _ _ _

-----

lemma angel_wins_at_play_of {pw : ℕ} {g : Game pw}
  (h : g.angel_wins) {n : ℕ} : (g.play n).angel_wins :=
begin
  intro k, specialize h (k + n),
  rw [Game.play, function.iterate_add] at h, exact h,
end

lemma angel_wins_at_play_move_of {pw : ℕ} {g : Game pw}
  (h : g.angel_wins) : g.play_move.angel_wins :=
@angel_wins_at_play_of _ _ h 1

lemma play_angel_move_at_players_eq {pw : ℕ} {g : Game pw} :
  (play_angel_move_at g).a = g.a ∧ (play_angel_move_at g).d = g.d :=
by { rw [play_angel_move_at], split_ifs; exact ⟨rfl, rfl⟩ }

lemma play_devil_move_at_players_eq {pw : ℕ} {g : Game pw} {hs} :
  (play_devil_move_at g hs).a = g.a ∧ (play_devil_move_at g hs).d = g.d :=
by { rw [play_devil_move_at], exact ⟨rfl, rfl⟩ }

lemma play_move_at_players_eq {pw : ℕ} {g : Game pw} :
  g.play_move.a = g.a ∧ g.play_move.d = g.d :=
begin
  rw [Game.play_move], split_ifs, swap, exact ⟨rfl, rfl⟩,
  rw [play_angel_move_at_players_eq.1, play_angel_move_at_players_eq.2],
  rw [play_devil_move_at_players_eq.1, play_devil_move_at_players_eq.2],
  exact ⟨rfl, rfl⟩,
end

lemma play_move_at_players_eq' {pw : ℕ} {g : Game pw} {hs} :
  (play_angel_move_at (play_devil_move_at g hs)).a = g.a ∧
  (play_angel_move_at (play_devil_move_at g hs)).d = g.d :=
by { rw play_angel_move_at, split_ifs; exact ⟨rfl, rfl⟩ }

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
  g.play_move = play_angel_move_at (play_devil_move_at g h) :=
dif_pos h

lemma play_move_at_not_act {pw : ℕ} {g : Game pw}
  (h : ¬g.act) :
  g.play_move = g :=
dif_neg h

lemma play_angel_move_hvm {pw : ℕ} {g : Game pw} (hs)
  (h : angel_has_valid_move pw g.s.board) :
  ∃ h, play_angel_move_at g = play_angel_move_at' g.a g hs h :=
by exact ⟨_, dif_pos ⟨hs, h⟩⟩

lemma play_angel_move_at_set_devil {pw : ℕ}
  {g : Game pw} {d₁ : Devil} :
  play_angel_move_at (g.set_devil d₁) = (play_angel_move_at g).set_devil d₁ :=
by { simp_rw play_angel_move_at, split_ifs; refl }

lemma play_devil_move_at_set_angel {pw pw₁ : ℕ}
  {g : Game pw} {a₁ : Angel pw₁} {hs} :
  play_devil_move_at (g.set_angel a₁) hs =
  (play_devil_move_at g hs).set_angel a₁ :=
rfl

lemma angel_has_valid_move_at_play_devil_move {pw : ℕ} {g : Game pw} {hs}
  (h : g.angel_wins) :
  angel_has_valid_move pw (play_devil_move_at g hs).s.board :=
begin
  specialize h 1, change g.play_move.act at h,
  rw play_move_at_act hs at h, rw play_angel_move_at at h,
  split_ifs at h with h₁,
  { exact h₁.2 },
  { cases h },
end

-----

lemma act_play_move_at_succ {pw : ℕ} {g : Game pw}
  (h : g.play_move.act) : g.act :=
by { rw Game.play_move at h, split_ifs at h with h₁; assumption }

lemma act_play_at_succ {pw n : ℕ} {g : Game pw}
  (h : (g.play n.succ).act) : (g.play n).act :=
by { rw play_at_succ' at h, exact act_play_move_at_succ h }

lemma act_play_at_ge {pw n m : ℕ} {g : Game pw}
  (h₁ : n ≤ m) (h₂ : (g.play m).act) : (g.play n).act :=
begin
  induction' h₁,
  { exact h₂ },
  { rw play_at_succ' at h₂, exact ih (act_play_move_at_succ h₂) },
end

lemma play_angel_move_at_hist_len_ge {pw : ℕ} {g : Game pw} :
  g.s.history.length ≤ (play_angel_move_at g).s.history.length :=
begin
  rw play_angel_move_at, split_ifs, swap, { refl },
  exact nat.le_of_lt (nat.lt_succ_self _),
end

lemma play_devil_move_at_hist_len_ge {pw : ℕ} {g : Game pw} {hs} :
  g.s.history.length ≤ (play_devil_move_at g hs).s.history.length :=
nat.le_of_lt (nat.lt_succ_self _)

lemma play_devil_move_at_hist_len_eq {pw : ℕ} {g : Game pw} {hs} :
  (play_devil_move_at g hs).s.history.length = g.s.history.length.succ :=
rfl

lemma play_move_at_hist_len_ge {pw : ℕ} {g : Game pw} :
  g.s.history.length ≤ g.play_move.s.history.length :=
begin
  rw Game.play_move, split_ifs with hs, swap, { refl },
  rw play_angel_move_at, split_ifs with h₁,
  { change (play_devil_move_at g hs).a with g.a,
    transitivity (play_devil_move_at g hs).s.history.length,
    { exact play_devil_move_at_hist_len_ge },
    { exact nat.le_of_lt (nat.lt_succ_self _) }},
  { exact nat.le_of_lt (nat.lt_succ_self _) },
end

lemma play_at_hist_len_ge {pw n : ℕ} {g : Game pw} :
  g.s.history.length ≤ (g.play n).s.history.length :=
begin
  induction n with n ih,
  { refl },
  { apply le_trans ih, clear ih, rw play_at_succ',
    exact play_move_at_hist_len_ge },
end

lemma set_players_flip {pw pw₁ : ℕ} {g : Game pw}
  {a₁ : Angel pw₁} {d₁ : Devil} :
  (g.set_angel a₁).set_devil d₁ = (g.set_devil d₁).set_angel a₁ :=
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

lemma play_devil_move_eq {pw : ℕ} {g : Game pw} {hs} :
  play_devil_move_at g hs =
  g.set_state (apply_devil_move g.s (g.d.f g.s hs).m) :=
rfl

-----

lemma set_prev_moves_angel_wins_iff {pw : ℕ} {g : Game pw}
  {fa : Angel_prev_moves pw g.s}
  {fd : Devil_prev_moves g.s} :
  (g.set_prev_moves fa fd).angel_wins ↔ g.angel_wins :=
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
  have h₁ : play_devil_move_at (g₁.set_players a' d') h =
    (play_devil_move_at g₁ h).set_players a' d',
  { simp_rw [Game.set_players, set_players_flip, play_devil_move_at_set_angel],
    congr, simp_rw play_devil_move_at,
    change (g₁.set_devil d').d with d',
    ext; try { refl }, change _ = apply_devil_move _ _,
    simp [apply_devil_move, apply_move], simp_rw Game.set_state,
    refine ⟨_, ⟨rfl, rfl⟩, rfl⟩, change (g₁.set_devil d').s with g₁.s,
    congr' 1, generalize_proofs, change d'.f g₁.s h with dite _ _ _,
    split_ifs with h₂,
    { exfalso, contrapose! h₂, clear h₂,
      transitivity (g.play n).s.history.length,
      { exact play_at_hist_len_ge },
      { refl }},
    { congr, exact play_at_players_eq.2.symm }},
  rw h₁, clear h₁,
  let g₂ : Game pw := _, change (play_devil_move_at g₁ h) with g₂,
  have h₁ : play_angel_move_at (g₂.set_angel a') =
    (play_angel_move_at g₂).set_angel a',
  { simp_rw play_angel_move_at,
    change dite (g₂.act ∧ angel_has_valid_move pw g₂.s.board) _ _ = _,
    split_ifs with hx, swap, { refl },
    change (g₂.set_angel a').a with a',
    simp_rw play_angel_move_at', ext; try {refl},
    simp_rw Game.set_state,
    change (g₂.set_angel a').s with g₂.s at hx ⊢,
    change _ = apply_angel_move _ _,
    simp [apply_angel_move, apply_move],
    generalize_proofs hy hz,
    change a'.f g₂.s h hy with dite _ _ _,
    split_ifs with h₂,
    { exfalso, contrapose! h₂, clear h₂,
      transitivity (g.play n).s.history.length,
      { exact play_at_hist_len_ge },
      { exact play_devil_move_at_hist_len_ge }},
    { congr, exact play_at_players_eq.1.symm }},
  simp_rw [Game.set_players, play_angel_move_at_set_devil, h₁],
end

lemma angel_set_move_angel_wins_iff {pw : ℕ} {g : Game pw}
  {s : State} {m : Valid_angel_move pw s.board}
  (h : s.history.length < g.s.history.length) :
  (g.set_angel (g.a.set_move s m)).angel_wins ↔ g.angel_wins :=
begin
  convert set_prev_moves_angel_wins_iff, ext,
  { change _ = g.a.prev_moves_set g.s s m h, rw angel_prev_moves_set_eq, refl },
  repeat { refl }, change _ = g.d.prev_moves_id g.s,
  rw devil_prev_moves_id_eq, refl,
end

lemma devil_set_move_angel_wins_iff {pw : ℕ} {g : Game pw}
  {s : State} {m : Valid_devil_move s.board}
  (h : s.history.length < g.s.history.length) :
  (g.set_devil (g.d.set_move s m)).angel_wins ↔ g.angel_wins :=
begin
  convert set_prev_moves_angel_wins_iff, ext,
  { change _ = g.a.prev_moves_id g.s, rw angel_prev_moves_id_eq, },
  repeat { refl }, change _ = g.d.prev_moves_set g.s s m h,
  rw devil_prev_moves_set_eq,
end

lemma play_1 {pw : ℕ} {g : Game pw} : g.play 1 = g.play_move :=
rfl

-----

lemma init_game_act {pw : ℕ}
  {a : Angel pw} {d : Devil} {s : State}
  (h : s.act) :
  (init_game a d s).act := h

lemma init_game_play_move {pw : ℕ}
  {a : Angel pw} {d : Devil} {s : State} (hs) :
  (init_game a d s).play_move =
  play_angel_move_at (play_devil_move_at (init_game a d s) hs) :=
dif_pos (init_game_act hs)

lemma angel_played_move_at_apply_move {pw : ℕ} {s s' : State}
  {md : Valid_devil_move s.board}
  {ma : Valid_angel_move pw s'.board}
  (h : s' = apply_devil_move s md.m) :
  angel_played_move_at (apply_angel_move s' ma.m) s' ma :=
begin
  sorry
  -- let a := (default : Angel pw).set_move s' ma,
  -- let d := (default : Devil).set_move s md,
  -- use [s, md, a, d, 1, h],
  -- change _ = (init_game a d s).play_move.s, rw init_game_play_move,
  -- have h₁ : play_devil_move_at (init_game a d s)  = init_game a d s',
  -- { ext; try { refl }, change apply_devil_move s (d.f s).m = s',
  --   rw h, congr, change dite _ _ _ = _, split_ifs; refl },
  -- rw h₁, clear h₁, rw play_angel_move_at, split_ifs with h₁,
  -- { change _ = apply_angel_move s' (a.f s' h₁).m,
  --   congr, symmetry, change dite _ _ _ = _, split_ifs; refl },
  -- { change (init_game a d s').s with s' at h₁,
  --   cases ma with m h₂, apply h₁.elim, exact ⟨m, h₂⟩ },
end

lemma angel_played_move_at_play_move {pw : ℕ}
  {g : Game pw} {s' : State} {ma : Valid_angel_move pw s'.board}
  (h : angel_played_move_at g.s s' ma) :
  angel_played_move_at g.play_move.s s' ma :=
begin
  rcases h with ⟨s, md, a, d, n, h₁, h₂⟩,
  by_cases h₃ : g.act,
  {
    sorry
  },
  {
    use [s, md, a, d, n, h₁],
    rw play_move_at_not_act h₃,
    exact h₂,
  },
end

-- #exit

lemma angel_played_move_at_play {pw n : ℕ}
  {g : Game pw} {s' : State} {ma : Valid_angel_move pw s'.board}
  (h : angel_played_move_at g.s s' ma) :
  angel_played_move_at (g.play n).s s' ma :=
begin
  induction n with n ih, { exact h },
  rw play_at_succ',
  exact angel_played_move_at_play_move ih,
end

lemma angel_played_move_at_eq {pw : ℕ}
  {sx s' : State} {ma₁ ma₂ : Valid_angel_move pw s'.board}
  (h₁ : angel_played_move_at sx s' ma₁)
  (h₂ : angel_played_move_at sx s' ma₂) :
  ma₁ = ma₂ :=
begin
  sorry
end