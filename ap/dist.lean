import tactic.induction
import data.int.basic
import data.set.basic

import .base .point

noncomputable theory
open_locale classical

-----

lemma dist_self {p} : dist p p = 0 :=
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

lemma dist_eq_zero_iff {p₁ p₂ : Point} : dist p₁ p₂ = 0 ↔ p₁ = p₂ :=
begin
  split; intro h,
  { obtain ⟨h₁, h₂⟩ := eq_zero_of_max_eq_zero h,
    rw sub_eq_zero at h₁ h₂, ext; assumption },
  { subst h, exact dist_self },
end