import tactic.induction
import data.int.basic
import data.set.basic
import logic.function.iterate

import .point .dist .board .state .move .player

noncomputable theory
open_locale classical

@[ext] structure Game (pw : ℕ) : Type :=
(a : Angel pw)
(d : Devil)
(s : State)
(act : Prop)

def init_game {pw : ℕ} (a : Angel pw) (d : Devil) : Game pw :=
{ a := a,
  d := d,
  s := state₀,
  act := true }

def Game.set_angel {pw pw₁ : ℕ} (g : Game pw) (a₁ : Angel pw₁) : Game pw₁ :=
{g with a := a₁}

def Game.set_devil {pw : ℕ} (g : Game pw) (d₁ : Devil) : Game pw :=
{g with d := d₁}

def Game.set_state {pw : ℕ} (g : Game pw) (s₁ : State) : Game pw :=
{g with s := s₁}

def play_angel_move_at' {pw pw₁ : ℕ} (a₁ : Angel pw₁) (g : Game pw) (h) :=
{g with s := apply_angel_move g.s (a₁.f g.s h).m}

def play_angel_move_at {pw : ℕ} (g : Game pw) :=
if h : angel_has_valid_move pw g.s.board
then play_angel_move_at' g.a g h
else {g with act := false}

def play_devil_move_at {pw : ℕ} (g : Game pw) :=
{g with s := apply_devil_move g.s (g.d.f g.s).m}

def Game.play_move {pw : ℕ} (g : Game pw) :=
if g.act then play_angel_move_at (play_devil_move_at g) else g

def Game.play {pw : ℕ} (g : Game pw) (n : ℕ) :=
(Game.play_move^[n]) g

def Game.angel_wins {pw : ℕ} (g : Game pw) :=
∀ (n : ℕ), (g.play n).act

def Game.devil_wins {pw : ℕ} (g : Game pw) :=
∃ (n : ℕ), ¬(g.play n).act

def angel_hws_at (pw : ℕ) (s : State) :=
∃ (a : Angel pw), ∀ (d : Devil), Game.angel_wins ⟨a, d, s, true⟩

def devil_hws_at (pw : ℕ) (s : State) :=
∃ (d : Devil), ∀ (a : Angel pw), Game.devil_wins ⟨a, d, s, true⟩

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

lemma play_devil_move_at_players_eq {pw : ℕ} {g : Game pw} :
  (play_devil_move_at g).a = g.a ∧ (play_devil_move_at g).d = g.d :=
by { rw [play_devil_move_at], exact ⟨rfl, rfl⟩ }

lemma play_move_at_players_eq {pw : ℕ} {g : Game pw} :
  g.play_move.a = g.a ∧ g.play_move.d = g.d :=
begin
  rw [Game.play_move], split_ifs, swap, exact ⟨rfl, rfl⟩,
  rw [play_angel_move_at_players_eq.1, play_angel_move_at_players_eq.2],
  rw [play_devil_move_at_players_eq.1, play_devil_move_at_players_eq.2],
  exact ⟨rfl, rfl⟩,
end

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
  g.play_move = play_angel_move_at (play_devil_move_at g) :=
if_pos h

lemma play_angel_move_hvm {pw : ℕ} {g : Game pw}
  (h : angel_has_valid_move pw g.s.board) :
  ∃ h, play_angel_move_at g = play_angel_move_at' g.a g h :=
by { rw [play_angel_move_at, dif_pos h], use h }

lemma play_devil_move_at_set_angel {pw pw₁ : ℕ}
  {g : Game pw} {a₁ : Angel pw₁} :
  play_devil_move_at (g.set_angel a₁) = (play_devil_move_at g).set_angel a₁ :=
rfl

lemma angel_has_valid_move_at_play_devil_move {pw : ℕ} {g : Game pw}
  (h : g.angel_wins) :
  angel_has_valid_move pw (play_devil_move_at g).s.board :=
begin
  specialize h 1, contrapose h,
  change ¬Game.act (ite _ _ _), split_ifs with h₁, swap, exact h₁,
  change ¬Game.act (dite _ _ _), split_ifs with h₁, exact not_false,
end

-----

lemma act_play_move_at_succ {pw : ℕ} {g : Game pw}
  (h : g.play_move.act) : g.act :=
by { contrapose h, change ¬Game.act (ite _ _ _), rwa if_neg h }

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