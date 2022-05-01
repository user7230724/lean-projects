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
  rw bounded_area,
  let s := {p : ℤ × ℤ | |p.1| ≤ n ∧ |p.2| ≤ n}, haveI : fintype s,
  { apply fintype_subtype_of_set_finite, let s : set ℤ := {k : ℤ | |k| ≤ n},
    have h : s.finite,
    { rw (_ : s = finset.Icc (-(n : ℤ)) n), swap,
      { ext, simp only [finset.coe_Icc, set.mem_set_of_eq,
        set.mem_Icc, abs_le] },
      exact (finset.Icc (-↑n) ↑n).finite_to_set },
    exact set.finite.prod h h },
  rw (_ : (bounded n).to_finset.card = s.to_finset.card), swap,
  { simp_rw set.to_finset_card, apply fintype.card_congr,
    fapply equiv.of_bijective,
    { rintro p, use ⟨p.1.1, p.1.2⟩, cases p with p h, dsimp,
      rw bounded at h, dsimp at h, simp [dist_le_iff, center] at h, exact h },
    { fsplit,
      { rintro p₁ p₂ h₁, dsimp at h₁, generalize_proofs h₂ h₃ at h₁,
        simp at h₁, cases h₁, ext; assumption },
      { rintro ⟨p, h⟩, fsplit,
        { use ⟨p.1, p.2⟩, simp [bounded], change s with {p : _ | _} at h,
          simp at h, simpa [dist_le_iff, center] },
        { simp }}}},
  let fs' := finset.Icc (-(n : ℤ)) n,
  rw (_ : s.to_finset = fs'.product fs'), swap,
  { ext p, rw set.mem_to_finset, change s with {p : _ | _}, dsimp,
    simp_rw [finset.mem_product, finset.mem_Icc, abs_le] },
  simp only [finset.card_product, int.card_Icc, sub_neg_eq_add],
  rw (_ : (n + 1 + n : ℤ).to_nat = n * 2 + 1), swap,
  { norm_cast, rw (by linarith : n + 1 + n = n * 2 + 1),
    apply int.to_nat_coe_nat },
  rw sq,
end

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