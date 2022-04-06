import tactic
import tactic.induction

import .base .game

def D_hws (pw : ℕ) := D_hws_at pw state₀

def Bound (r : ℕ) : set Point :=
{p : Point | dist p center ≤ r}

def trapped_in {pw : ℕ} (a : A pw) (d : D) (B : set Point) : Prop :=
∀ (n : ℕ), ((init_game a d state₀).play n).s.board.A ∈ B

lemma lem_2_1 {pw : ℕ}
  (h : D_hws pw) :
  ∃ (N : ℕ) (d : D), ∀ (a : A pw),
  trapped_in a d (Bound N) :=
begin
  sorry
end