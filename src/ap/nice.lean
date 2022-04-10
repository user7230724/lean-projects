import tactic
import tactic.induction

import .base .lemma_2_1

noncomputable theory
open_locale classical

def A_trapped_in (pw : ℕ) (s : State) (B : set Point) :=
∀ (a : A pw) (d : D) (n : ℕ), ((init_game a d s).play n).s.board.A ∈ B

def A_trapped (pw : ℕ) (s : State) :=
∃ (B : set Point), A_trapped_in pw s B

def D.nice (d : D) (pw : ℕ) :=
∀ (s : State) (hs : s.act) (p : Point) (b : Board),
¬A_trapped pw s →
(d.f s hs).m = some p →
b ∈ s.history →
pw < dist p b.A