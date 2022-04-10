import tactic.induction
import data.int.basic
import data.set.basic

import .base

noncomputable theory
open_locale classical

instance : inhabited Point := ⟨center⟩

def Point_equiv_prod : Point ≃ ℤ × ℤ :=
begin
  fapply equiv.of_bijective, { intro p, exact ⟨p.1, p.2⟩ }, fsplit,
  { rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h₁, cases h₁; refl },
  { rintro ⟨x, y⟩, use ⟨x, y⟩ },
end

lemma Point_equiv_symm_apply {p : ℤ × ℤ} :
  Point_equiv_prod.symm.to_fun p = ⟨p.1, p.2⟩ :=
begin
  let e := Point_equiv_prod, convert_to e.inv_fun _ = _, dsimp,
  have h : e.to_fun (e.inv_fun p) = e.to_fun ⟨p.1, p.2⟩,
  { rw e.right_inv, ext; refl },
  exact e.left_inv.injective h,
end

lemma Point_equiv_symm_apply_x {p : ℤ × ℤ} :
  (Point_equiv_prod.symm.to_fun p).x = p.1 :=
by { rw Point_equiv_symm_apply }

lemma Point_equiv_symm_apply_y {p : ℤ × ℤ} :
  (Point_equiv_prod.symm.to_fun p).y = p.2 :=
by { rw Point_equiv_symm_apply }