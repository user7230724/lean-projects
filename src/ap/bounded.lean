import tactic
import tactic.induction

import .util .defs .dist

noncomputable theory
open_locale classical

def bounded (n : ℕ) : set Point :=
{p : Point | dist p center ≤ n}

-----

lemma finite_bounded {n : ℕ} : (bounded n).finite :=
dist_le_set_finite

instance {n : ℕ} : fintype (bounded n) :=
fintype_subtype_of_set_finite finite_bounded

def bounded_area (n : ℕ) : ℕ :=
(bounded n).to_finset.card

def squares_in_bounded (b : Board) (n : ℕ) : ℕ :=
((bounded n).to_finset.filter (λ p, p ∈ b.squares)).card

def squares_in_bounded_exc_A (b : Board) (n : ℕ) : ℕ :=
((bounded n).to_finset.filter (λ p, p ∈ b.squares ∧ p ≠ b.A)).card

-----

lemma mem_bounded_ge {n k : ℕ} {p : Point}
  (h₁ : p ∈ bounded k)
  (h₂ : k ≤ n) :
  p ∈ bounded n :=
by { simp [bounded] at h₂ ⊢, exact le_trans h₁ h₂ }

lemma bounded_area_eq {n : ℕ} :
  bounded_area n = (n * 2 + 1) ^ 2 :=
begin
  sorry
end

#exit

lemma squares_in_bounded_le_area {n : ℕ} {b : Board} :
  squares_in_bounded b n ≤ bounded_area n :=
begin
  apply finset.card_le_card_of_inj_on id; rintro p hp,
  { rw finset.mem_filter at hp, tauto },
  { tauto },
end

lemma squares_in_bounded_exc_A_le_area {n : ℕ} {b : Board} :
  squares_in_bounded_exc_A b n ≤ bounded_area n :=
begin
  refine le_trans _ squares_in_bounded_le_area, { exact b },
  rw [squares_in_bounded, squares_in_bounded_exc_A],
  apply finset.card_le_card_of_inj_on id; rintro p hp,
  { rw finset.mem_filter at hp ⊢, tauto },
  { tauto },
end