import tactic
import tactic.induction
import data.int.basic
import data.set.basic
import logic.function.iterate
import data.list

import .util .point .dist .board .state .player

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

def angel_played_move_at {pw : ℕ} (s : State) (s₀' : State)
  (ma : Valid_angel_move pw s₀'.board) : Prop :=
∃ (s₀ : State) (md : Valid_devil_move s₀.board) (a : Angel pw) (d : Devil) (n : ℕ),
s₀' = apply_devil_move s₀ md.m ∧ (∃ hs h, a.f s₀' hs h = ma) ∧
n ≠ 0 ∧ s = ((init_game a d s₀).play n).s

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

lemma act_play_at_le {pw n m : ℕ} {g : Game pw}
  (h₁ : n ≤ m) (h₂ : (g.play m).act) : (g.play n).act :=
begin
  induction' h₁,
  { exact h₂ },
  { rw play_at_succ' at h₂, exact ih (act_play_move_at_succ h₂) },
end

lemma hist_len_play_angel_move_at' {pw pw₁ : ℕ} {g : Game pw}
  {a₁ : Angel pw₁} {h₁ h₂} :
  (play_angel_move_at' a₁ g h₁ h₂).s.history.length = g.s.history.length.succ :=
hist_len_apply_angel_move

lemma hist_len_play_devil_move_at {pw : ℕ} {g : Game pw} {hs} :
  (play_devil_move_at g hs).s.history.length = g.s.history.length.succ :=
hist_len_apply_devil_move

lemma play_angel_move_at_hist_len_ge {pw : ℕ} {g : Game pw} :
  g.s.history.length ≤ (play_angel_move_at g).s.history.length :=
begin
  rw play_angel_move_at, split_ifs, swap, { refl },
  rw hist_len_play_angel_move_at',
  exact nat.le_of_lt (nat.lt_succ_self _),
end

lemma play_devil_move_at_hist_len_ge {pw : ℕ} {g : Game pw} {hs} :
  g.s.history.length ≤ (play_devil_move_at g hs).s.history.length :=
by { rw hist_len_play_devil_move_at, exact nat.le_of_lt (nat.lt_succ_self _) }

lemma play_devil_move_at_hist_len_eq {pw : ℕ} {g : Game pw} {hs} :
  (play_devil_move_at g hs).s.history.length = g.s.history.length.succ :=
by rw hist_len_play_devil_move_at

lemma play_move_at_hist_len_ge {pw : ℕ} {g : Game pw} :
  g.s.history.length ≤ g.play_move.s.history.length :=
begin
  rw Game.play_move, split_ifs with hs, swap, { refl },
  rw play_angel_move_at, split_ifs with h₁,
  { change (play_devil_move_at g hs).a with g.a,
    transitivity (play_devil_move_at g hs).s.history.length,
    { exact play_devil_move_at_hist_len_ge },
    { rw hist_len_play_angel_move_at',
      exact nat.le_of_lt (nat.lt_succ_self _) }},
  { change _ ≤ (play_devil_move_at g hs).s.history.length,
    rw hist_len_play_devil_move_at,
    exact nat.le_of_lt (nat.lt_succ_self _) },
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
    refine ⟨_, snoc_eq_snoc_iff.mpr ⟨rfl, rfl⟩, rfl⟩,
    change (g₁.set_devil d').s with g₁.s,
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

lemma play_1 {pw : ℕ} {g : Game pw} : g.play 1 = g.play_move := rfl

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
  let d := (default : Devil).set_move s md,
  use [s, md, a, d, 1, h], have hs₁ : s'.act := by rwa h,
  have hvm_s' : angel_has_valid_move pw s'.board := ⟨_, ma.h⟩,
  refine ⟨_, _, _⟩, { exact ⟨hs₁, hvm_s', angel_set_move_eq_pos⟩ },
  { dec_trivial }, rw [play_1, play_move_at_act], swap, { exact hs },
  rw play_angel_move_at, rw dif_pos, swap,
  { use hs, convert hvm_s', convert h.symm,
    change apply_devil_move s (d.f s hs).m = _, congr,
    exact devil_set_move_eq_pos },
  symmetry, change apply_angel_move _ _ = _,
  have h₁ : (play_devil_move_at (init_game a d s) hs).s = s',
  { convert h.symm, change apply_devil_move s (d.f s hs).m = _,
    congr, exact devil_set_move_eq_pos },
  congr' 1, change (a.f _ _ _).m = _, generalize_proofs h₂,
  have h₃ : (a.f (play_devil_move_at (init_game a d s) hs).s hs h₂).m =
    (a.f s' hs₁ hvm_s').m, { congr' },
  rw [h₃, angel_set_move_eq_pos],
end

lemma angel_hvm_of_next_act {pw : ℕ} {g : Game pw}
  (h : g.play_move.act) :
  ∃ hs, angel_has_valid_move pw (play_devil_move_at g hs).s.board :=
begin
  have hs : g.act := act_play_move_at_succ h, use hs,
  rw Game.play_move at h, rw dif_pos hs at h,
  rw play_angel_move_at at h, split_ifs at h with h₄,
  { cases h₄ with h₄ h₅, convert h₅, },
  { cases h }
end

lemma play_move_hist_len_eq_of_act {pw : ℕ} {g : Game pw}
  (h : g.play_move.act) :
  g.play_move.s.history.length = g.s.history.length + 2 :=
begin
  have h₁ : g.act := act_play_move_at_succ h,
  rw [play_move_at_act h₁, play_angel_move_at],
  rw dif_pos, { rw [hist_len_play_angel_move_at', hist_len_play_devil_move_at] },
  exact ⟨h₁, (angel_hvm_of_next_act h).some_spec⟩,
end

lemma play_hist_len_eq_of_act {pw n : ℕ} {g : Game pw}
  (h : (g.play n).act) :
  (g.play n).s.history.length = g.s.history.length + n * 2 :=
begin
  induction n with n ih, { refl }, rw play_at_succ' at h ⊢,
  let g₁ : Game pw := _, change g.play n with g₁ at ih h ⊢,
  have h₁ := act_play_move_at_succ h, specialize ih h₁,
  rw [play_move_hist_len_eq_of_act h, ih, add_assoc, nat.succ_mul],
end

lemma hist_len_ne_of_play_lt {pw n k : ℕ} {g : Game pw}
  (h₁ : k < n) (h₂ : (g.play n).act) :
  (g.play k).s.history.length ≠ (g.play n).s.history.length :=
begin
  have h₃ := act_play_at_le (nat.le_of_lt h₁) h₂,
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

lemma apply_angel_move_ne_of_hist_ne {pw : ℕ} {s₁ s₂ : State}
  {ma₁ ma₂ : Angel_move} (h : s₁.history.length ≠ s₂.history.length) :
  apply_angel_move s₁ ma₁ ≠ apply_angel_move s₂ ma₂ :=
begin
  contrapose! h, simp_rw [apply_angel_move, apply_move] at h,
  rw (snoc_eq_snoc_iff.mp h.2.1).1,
end

lemma apply_devil_move_ne_of_hist_ne {s₁ s₂ : State}
  {md₁ md₂ : Devil_move} (h : s₁.history.length ≠ s₂.history.length) :
  apply_devil_move s₁ md₁ ≠ apply_devil_move s₂ md₂ :=
begin
  contrapose! h, simp_rw [apply_devil_move, apply_move] at h,
  rw (snoc_eq_snoc_iff.mp h.2.1).1,
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
  let a := g.a, let d := g.d, let s := g.s,
  rcases h with ⟨s₀, md₀, a₀, d₀, n, h₁, hx, hy, h₂⟩, by_cases hs : g.act,
  { let md := d.f s hs, let s' := apply_devil_move s md.m,
    let d₁ := d₀.set_move s md,
    let a₁ := mk_angel_for_played_move_at_play_move a₀ a s' hs,
    use [s₀, md₀, a₁, d₁, n.succ, by rw h₁],
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
      { apply act_play_at_le (nat.le_of_succ_le hk),
        change ((init_game a₀ d₀ s₀).play n).s.act,
        rw ←h₂, exact hs },
      repeat { rw play_move_at_act, swap, { exact hs₁ }},
      let g₁ : Game pw := _,
      change (init_game a₀ d₀ s₀).play k with g₁ at hs₁ ⊢,
      have ha : g₁.a = a₀ := play_at_players_eq.1,
      have hd : g₁.d = d₀ := play_at_players_eq.2,
      let sk := g₁.s, let mdk := d₀.f sk hs₁,
      let sk' := apply_devil_move sk mdk.m,
      have hy : (play_devil_move_at g₁ hs₁).s = sk',
      { change apply_devil_move sk _ = apply_devil_move _ _, congr' 2, rw hd },
      have h₁ : d₁.f sk hs₁ = mdk,
      { change dite _ _ _ = _, rw dif_neg,
        change ((init_game a₀ d₀ s₀).play k).s ≠ g.s, rw h₂,
        apply state_ne_of_play_lt (nat.succ_le_iff.mp hk),
        change ((init_game a₀ d₀ s₀).play n).s.act, rw ←h₂, exact hs },
      have hx : play_devil_move_at (g₁.set_players a₁ d₁) hs₁ =
        (play_devil_move_at g₁ hs₁).set_players a₁ d₁,
      { ext,
        { exact play_devil_move_at_players_eq.1, },
        { exact play_devil_move_at_players_eq.2, },
        { change apply_devil_move g₁.s _ = apply_devil_move _ _,
          congr' 2, change d₁.f sk _ = _, rw [h₁, hd] }},
      rw hx, clear hx, have hx : angel_has_valid_move pw sk'.board,
      { have h₃ : g₁.play_move.act,
        { change ((init_game a₀ d₀ s₀).play k).play_move.act,
          rw ←play_at_succ', apply act_play_at_le hk,
          change ((init_game a₀ d₀ s₀).play n).s.act,
          rw ←h₂, exact hs },
        convert (angel_hvm_of_next_act h₃).some_spec, rw ←hy, refl },
      simp_rw play_angel_move_at,
      repeat { rw dif_pos, swap, { use hs₁, convert hx }},
      change apply_angel_move (play_devil_move_at g₁ hs₁).s
        (a₁.f (play_devil_move_at g₁ hs₁).s _ _).m =
        apply_angel_move _ (g₁.a.f (play_devil_move_at g₁ hs₁).s _ _).m,
      congr' 2, rw ha, generalize_proofs h₃,
      change (mk_angel_for_played_move_at_play_move _ _ _ _).f _ _ _ = _,
      rw mk_angel_for_played_move_at_play_move,
      split_ifs with hh, swap, { refl },
      change dite _ _ _ = _, rw dif_neg, rw hy,
      change apply_devil_move ((init_game a₀ d₀ s₀).play k).s mdk.m ≠
        apply_devil_move g.s md.m,
      rw h₂, replace hk := nat.lt_of_succ_le hk,
      apply apply_devil_move_ne_of_hist_ne, apply hist_len_ne_of_play_lt hk,
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
      change (mk_angel_for_played_move_at_play_move _ _ _ _).f _ _ _ = _,
      rw mk_angel_for_played_move_at_play_move,
      split_ifs with hss, swap, { refl }, change dite _ _ _ = _,
      rw dif_neg, change s₀' ≠ apply_devil_move g.s _, rw [h₁, h₂],
      apply apply_devil_move_ne_of_hist_ne,
      change ((init_game a₀ d₀ s₀).play 0).s.history.length ≠ _,
      apply hist_len_ne_of_play_lt (pos_iff_ne_zero.mpr hy),
      rw [Game.act, ←h₂], exact hs }, { dec_trivial }, symmetry,
    have h₁ : play_devil_move_at (g.set_players a₁ d₁) hs =
      (play_devil_move_at g hs).set_players a₁ d₁,
    { ext,
      { exact play_devil_move_at_players_eq.1 },
      { exact play_devil_move_at_players_eq.2 },
      { change apply_devil_move g.s _ = apply_devil_move _ _,
        congr' 2, change d₁.f s hs = g.d.f g.s hs,
        change dite _ _ _ = _, rw dif_pos rfl }},
    rw h₁, clear h₁, simp_rw play_angel_move_at,
    split_ifs with h₁, swap, { refl }, cases h₁ with h₁ h₂,
    change apply_angel_move ((play_devil_move_at g hs).s) _ =
      apply_angel_move _ _,
    congr' 2, change a₁.f s' _ _ = a.f s' _ _, generalize_proofs,
    change (mk_angel_for_played_move_at_play_move _ _ _ _).f _ _ _ = _,
    rw mk_angel_for_played_move_at_play_move, rw dif_pos, swap, { exact h₂ },
    change dite _ _ _ = _, rw dif_pos rfl },
  { use [s₀, md₀, a₀, d₀, n, h₁, hx, hy], rw play_move_at_not_act hs, exact h₂ },
end

lemma angel_played_move_at_play {pw n : ℕ}
  {g : Game pw} {s' : State} {ma : Valid_angel_move pw s'.board}
  (h : angel_played_move_at g.s s' ma) :
  angel_played_move_at (g.play n).s s' ma :=
begin
  induction n with n ih, { exact h }, rw play_at_succ',
  exact angel_played_move_at_play_move ih,
end

lemma hist_len_game_finish {pw : ℕ} {g : Game pw} :
  g.finish.s.history.length = g.s.history.length := rfl

lemma hist_len_le_play_move {pw : ℕ} {g : Game pw} :
  g.s.history.length ≤ g.play_move.s.history.length :=
begin
  rw Game.play_move, split_ifs with hs, swap, { refl },
  rw play_angel_move_at, split_ifs with h,
  { rw [hist_len_play_angel_move_at', hist_len_play_devil_move_at],
    apply nat.le_succ_of_le (nat.le_succ _) },
  { rw [hist_len_game_finish, hist_len_play_devil_move_at],
    apply nat.le_succ },
end

lemma hist_len_le_play {pw n : ℕ} {g : Game pw} :
  g.s.history.length ≤ (g.play n).s.history.length :=
begin
  induction n with n ih, { refl }, rw play_at_succ',
  exact ih.trans hist_len_le_play_move,
end

lemma hist_overlaps_of_angel_played_move_at {pw : ℕ}
  {s s₀' : State} {ma : Valid_angel_move pw s₀'.board}
  (h₁ : angel_played_move_at s s₀' ma) :
  ∀ (k : ℕ), k.succ < s₀'.history.length →
  s.history.nth k = s₀'.history.nth k :=
begin
  rintro k h₂, rcases h₁ with ⟨s₀, md, a, d, n, rfl, hx, hy, rfl⟩, clear' hx hy,
  change (apply_devil_move s₀ md.m).history with (_ ++ _ : list _) at h₂ ⊢,
  rw [length_snoc, nat.succ_lt_succ_iff] at h₂, induction n with n ih,
  { change s₀.history.nth k = _, exact (list.nth_append h₂).symm },
  { simp_rw play_at_succ', let g : Game pw := _,
    change (init_game a d s₀).play n with g at h₂ ih ⊢, rw ←ih, clear ih,
    rw Game.play_move, split_ifs with hs, swap, { refl }, rw play_angel_move_at,
    have h₆ : s₀.history.length ≤ g.s.history.length,
    { change (init_game a d s₀).s.history.length ≤ _, exact hist_len_le_play },
    split_ifs with h₃,
    { change (_ ++ _ : list _).nth _ = _, rw list.nth_append,
      { change (_ ++ _ : list _).nth _ = _, rw list.nth_append,
        exact gt_of_ge_of_gt h₆ h₂ },
      { rw hist_len_play_devil_move_at,
        exact nat.lt_succ_of_le (nat.le_trans (le_of_lt h₂) h₆) }},
    { change (_ ++ _ : list _).nth _ = _, rw list.nth_append,
      exact gt_of_ge_of_gt h₆ h₂ }},
end

lemma angel_played_move_at_eq_aux {pw n : ℕ}
  {sx s₀ s' : State} {md : Valid_devil_move s₀.board}
  {a : Angel pw} {d : Devil} {hs hvm}
  (h₁ : s' = apply_devil_move s₀ md.m)
  (h₂ : sx = ((init_game a d s₀).play n).s)
  (h₃ : n ≠ 0) :
  sx.history.nth (s₀.history.length + 2) = option.some
    (apply_angel_move s' (a.f s' hs hvm).m).board :=
begin
  sorry
end

#exit

lemma angel_played_move_at_eq {pw : ℕ}
  {sx s' : State} {ma₁ ma₂ : Valid_angel_move pw s'.board}
  (hx : angel_played_move_at sx s' ma₁)
  (hy : angel_played_move_at sx s' ma₂) :
  ma₁ = ma₂ :=
begin
  obtain ⟨s₀, md₁, a₁, d₁, n₁, h₁, ⟨hs₁, hvm₁, rfl⟩, h₃, h₄⟩ := hx,
  obtain ⟨s₀', md₂, a₂, d₂, n₂, h₅, ⟨hs₂, hvm₂, rfl⟩, h₇, h₈⟩ := hy,
  obtain rfl : s₀ = s₀',
  { subst h₁, exact state_eq_of_apply_devil_move_eq h₅ },
  obtain rfl : md₁ = md₂,
  { subst h₁, rwa ←devil_moves_eq_iff at h₅ },
  clear h₅, change hvm₂ with hvm₁, clear hvm₂,
  change hs₂ with hs₁, clear hs₂, let i := s₀.history.length,
  have h₅ : sx.history.nth (i + 2) = option.some
    (apply_angel_move s' (a₁.f s' hs₁ hvm₁).m).board,
  { exact angel_played_move_at_eq_aux h₁ h₄ h₃ },
  have h₆ : sx.history.nth (i + 2) = option.some
    (apply_angel_move s' (a₂.f s' hs₁ hvm₁).m).board,
  { exact angel_played_move_at_eq_aux h₁ h₈ h₇ },
  simp [h₅] at h₆, rwa angel_moves_eq_iff',
end