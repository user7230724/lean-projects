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
  {md : Valid_devil_move s.board} {ma : Valid_angel_move pw s'.board}
  (hs : s.act) (h : s' = apply_devil_move s md.m) :
  angel_played_move_at (apply_angel_move s' ma.m) s' ma :=
begin
  let a := (default : Angel pw).set_move s' ma,
  let d := (default : Devil).set_move s md, use [s, md, a, d, 1, h],
  rw [play_1, play_move_at_act], swap, { exact hs }, rw play_angel_move_at,
  have h₄ : (play_devil_move_at (init_game a d s) hs).s = s',
  { symmetry, convert h, rw play_devil_move_at, change apply_devil_move _ _ = _,
    congr, change dite _ _ _ = _, rw dif_pos; refl },
  split_ifs with h₁,
  { cases h₁ with h₂ h₃, rw play_devil_move_at_players_eq.1,
    change (init_game a d s).a with a, generalize_proofs,
    change _ = apply_angel_move _ _, simp_rw h₄, congr, { exact h₄.symm },
    symmetry, have hs₁ : s'.act, { rw ←h₄, exact hs },
    have h₅ : a.f s' hs₁ ⟨_, ma.h⟩ == ma,
    { change dite _ _ _ == _, rw dif_pos rfl },
    convert h₅ },
  { contrapose! h₁, clear h₁, split, { assumption },
    suffices h₁ : angel_has_valid_move pw s'.board, { convert h₁, },
    exact ⟨_, ma.h⟩ },
end

def mk_angel_for_played_move_at_play_move {pw : ℕ}
  (a₀ a : Angel pw) (s' : State) (hs : s'.act) :
  Angel pw :=
if hvm : angel_has_valid_move pw s'.board
then a₀.set_move s' (a.f s' hs hvm)
else a₀

lemma angel_played_move_at_play_move {pw : ℕ}
  {g : Game pw} {s₀' : State} {ma : Valid_angel_move pw s₀'.board}
  (h : angel_played_move_at g.s s₀' ma) :
  angel_played_move_at g.play_move.s s₀' ma :=
begin
  let a := g.a,
  let d := g.d,
  let s := g.s,
  rcases h with ⟨s₀, md₀, a₀, d₀, n, h₁, h₂⟩,
  by_cases hs : g.act,
  {
    let md := d.f s hs,
    let s' := apply_devil_move s md.m,
    let d₁ := d₀.set_move s md,
    let a₁ := mk_angel_for_played_move_at_play_move a₀ a s' hs,
    use [s₀, md₀, a₁, d₁, n.succ, by rw h₁],
    have h₁ : ∀ (k ≤ n), ((init_game a₁ d₁ s₀).play k).s =
      ((init_game a₀ d₀ s₀).play k).s,
    {
      rintro k hk,
      induction k with k ih, { refl },
      simp_rw play_at_succ',
      specialize ih (nat.le_of_succ_le hk),
      replace ih : (init_game a₁ d₁ s₀).play k =
        ((init_game a₀ d₀ s₀).play k).set_players a₁ d₁,
      sorry,
      -- {
      --   ext,
      --   {
      --     exact play_at_players_eq.1,
      --   },
      --   {
      --     exact play_at_players_eq.2,
      --   },
      --   {
      --     rw ih,
      --     refl,
      --   },
      -- },
      rw ih, clear ih,
      have hs₁ : ((init_game a₀ d₀ s₀).play k).act,
      sorry,
      repeat { rw play_move_at_act, swap, { exact hs₁ }},
      let g₁ : Game pw := _,
      change (init_game a₀ d₀ s₀).play k with g₁ at hs₁ ⊢,
      have ha : g₁.a = a₀ := play_at_players_eq.1,
      have hd : g₁.d = d₀ := play_at_players_eq.2,
      let sk := g₁.s,
      let mdk := d₀.f sk hs₁,
      let sk' := apply_devil_move sk mdk.m,
      have h₁ : d₁.f sk hs₁ = mdk,
      sorry,
      have h₂ : play_devil_move_at (g₁.set_players a₁ d₁) hs₁ =
        (play_devil_move_at g₁ hs₁).set_players a₁ d₁,
      sorry,
      rw h₂, clear h₂,
      have h₂ : angel_has_valid_move pw sk'.board,
      sorry,
      simp_rw play_angel_move_at,
      rw dif_pos,
      swap, sorry;{
        -- use hs₁, convert h₂,
        -- change apply_devil_move _ _ = apply_devil_move _ _,
        -- congr' 2,
        -- rw hd,
      },
      rw dif_pos,
      swap, sorry;{
        -- use hs₁, convert h₂,
        -- change apply_devil_move _ _ = apply_devil_move _ _,
        -- congr' 2,
        -- rw hd,
      },
      change apply_angel_move (play_devil_move_at g₁ hs₁).s
        (a₁.f (play_devil_move_at g₁ hs₁).s _ _).m =
        apply_angel_move _ (g₁.a.f (play_devil_move_at g₁ hs₁).s _ _).m,
      congr' 2, rw ha,
      generalize_proofs h₃,
      change (mk_angel_for_played_move_at_play_move _ _ _ _).f _ _ _ = _,
      rw mk_angel_for_played_move_at_play_move,
      rw dif_pos,
      swap, sorry,
      have h₄ : (play_devil_move_at g₁ hs₁).s = sk',
      sorry,
      change dite _ _ _ = _,
      rw dif_neg,
      rw h₄,
      change apply_devil_move g₁.s mdk.m ≠ apply_devil_move g.s md.m,
      sorry
    },
    sorry
    -- specialize h₁ n (le_refl n),
    -- replace h₁ : (init_game a₁ d₁ s₀).play n = g.set_players a₁ d₁,
    -- {
    --   ext,
    --   {
    --     exact play_at_players_eq.1,
    --   },
    --   {
    --     exact play_at_players_eq.2,
    --   },
    --   {
    --     rw h₁,
    --     exact h₂.symm,
    --   },
    -- },
    -- rw play_at_succ',
    -- rw play_move_at_act hs,
    -- rw h₁, clear h₁,
    -- rw play_move_at_act, swap, { exact hs },
    -- symmetry,
    -- have h₁ : play_devil_move_at (g.set_players a₁ d₁) hs =
    --   (play_devil_move_at g hs).set_players a₁ d₁,
    -- {
    --   ext,
    --   {
    --     exact play_devil_move_at_players_eq.1,
    --   },
    --   {
    --     exact play_devil_move_at_players_eq.2,
    --   },
    --   {
    --     change apply_devil_move g.s _ = apply_devil_move _ _,
    --     congr' 2,
    --     change d₁.f s hs = g.d.f g.s hs,
    --     change dite _ _ _ = _,
    --     rw dif_pos rfl,
    --   },
    -- },
    -- rw h₁, clear h₁,
    -- simp_rw play_angel_move_at,
    -- split_ifs with h₁, swap, { refl },
    -- cases h₁ with h₁ h₂,
    -- change apply_angel_move ((play_devil_move_at g hs).s) _ =
    --   apply_angel_move _ _,
    -- congr' 2,
    -- change a₁.f s' _ _ = a.f s' _ _,
    -- generalize_proofs,
    -- change (mk_angel_for_played_move_at_play_move _ _ _ _).f _ _ _ = _,
    -- rw mk_angel_for_played_move_at_play_move,
    -- rw dif_pos, swap, { exact h₂ },
    -- change dite _ _ _ = _,
    -- rw dif_pos rfl,
  },
  {
    sorry
    -- use [s₀, md₀, a₀, d₀, n, h₁],
    -- rw play_move_at_not_act h₃,
    -- exact h₂,
  },
end

#exit

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