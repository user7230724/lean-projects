import tactic.induction
import data.int.basic
import data.set.basic

import .base .point

noncomputable theory
open_locale classical

def Bounded (N : ℕ) : set Point :=
{p : Point | dist p center ≤ N}

def area_of_Bounded (N : ℕ) : ℕ :=
(N * 2 + 1) ^ 2

-----

lemma dist_self {a : Point} : dist a a = 0 :=
begin
  change int.to_nat _ = 0,
  simp_rw [sub_self, abs_zero, max_self], refl,
end

lemma eq_zero_left_of_max_eq_zero {a b : ℤ}
  (h : (max (|a|) (|b|)).to_nat = 0) : a = 0 :=
begin
  by_contra h₁,
  replace h₁ := lt_max_of_lt_left (abs_pos.mpr h₁),
  replace h₁ : int.to_nat 0 < (max (|a|) (|b|)).to_nat,
  { rw int.to_nat_lt_to_nat; assumption },
  rw h at h₁, cases h₁,
end

lemma eq_zero_right_of_max_eq_zero {a b : ℤ}
  (h : (max (|a|) (|b|)).to_nat = 0) : b = 0 :=
by { rw max_comm at h, exact eq_zero_left_of_max_eq_zero h }

lemma eq_zero_of_max_eq_zero {a b : ℤ}
  (h : (max (|a|) (|b|)).to_nat = 0) : a = 0 ∧ b = 0 :=
⟨eq_zero_left_of_max_eq_zero h, eq_zero_right_of_max_eq_zero h⟩

lemma dist_eq_zero_iff {a b : Point} : dist a b = 0 ↔ a = b :=
begin
  split; intro h,
  { obtain ⟨h₁, h₂⟩ := eq_zero_of_max_eq_zero h,
    rw sub_eq_zero at h₁ h₂, ext; assumption },
  { subst h, exact dist_self },
end

lemma dist_coe_int {a b : Point} :
  (dist a b : ℤ) = max (|a.x - b.x|) (|a.y - b.y|) :=
begin
  rw [dist, int.to_nat_eq_max, max_def, if_pos],
  rw max_def, split_ifs; apply abs_nonneg,
end

lemma triangle_aux {a b x y : ℤ} :
  |a + b| ≤ max (|a|) x + max (|b|) y :=
begin
  calc |a + b| ≤ |a| + |b| : abs_add _ _
  ... ≤ max (|a|) x + |b| : add_le_add_right (le_max_left _ _) _
  ... ≤ max (|a|) x + max (|b|) y : add_le_add_left (le_max_left _ _) _
end

lemma dist_triangle {a b c : Point} :
  dist a c ≤ dist a b + dist b c :=
begin
  zify, simp_rw [dist_coe_int, max_le_iff], split,
  { have h := @triangle_aux (a.x - b.x) (b.x - c.x) (|a.y - b.y|) (|b.y - c.y|),
    simp at h, exact h },
  { have h := @triangle_aux (a.y - b.y) (b.y - c.y) (|a.x - b.x|) (|b.x - c.x|),
    simp [max_comm] at h, exact h },
end

lemma dist_comm {a b : Point} : dist a b = dist b a :=
by { simp_rw dist, congr' 2; apply abs_sub_comm }

lemma dist_le_iff_zify {a b : Point} {d : ℕ} :
  dist a b ≤ d ↔ max (|a.x - b.x|) (|a.y - b.y|) ≤ d :=
by { simp [dist] }

lemma dist_le_iff {a b : Point} {d : ℕ} :
  dist a b ≤ d ↔ |a.x - b.x| ≤ d ∧ |a.y - b.y| ≤ d :=
by simp [dist_le_iff_zify]

lemma dist_le_set_finite {c : Point} {d : ℕ} :
  {p : Point | dist p c ≤ d}.finite :=
begin
  simp_rw dist_le_iff, apply set_finite_of_set_equiv_finite Point_equiv_prod.symm,
  convert_to {p : ℤ × ℤ | (|p.1 - c.x|) ≤ d ∧ (|p.2 - c.y|) ≤ d}.finite,
  { rw set.ext_iff, intro p, change _ ∧ _ ↔ _ ∧ _, rw iff_iff_eq,
    congr; rw Point_equiv_symm_apply },
  apply @set.finite.prod ℤ ℤ {x : ℤ | |x - c.x| ≤ ↑d} {y : ℤ | |y - c.y| ≤ ↑d};
  exact abs_sub_le_finite,
end

lemma mem_Bounded_ge {n k : ℕ} {p : Point}
  (h₁ : p ∈ Bounded k)
  (h₂ : k ≤ n) :
  p ∈ Bounded n :=
by { simp [Bounded] at h₂ ⊢, exact le_trans h₁ h₂ }