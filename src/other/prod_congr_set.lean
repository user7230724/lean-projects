import tactic
import tactic.induction

noncomputable theory
open_locale classical

@[to_additive]
lemma finset_prod_congr_set
  {α : Type*} [comm_monoid α] {β : Type*} [fintype β] (s : set β) (f : β → α) (g : s → α)
  (w : ∀ (x : β) (h : x ∈ s), f x = g ⟨x, h⟩) (w' : ∀ (x : β), x ∉ s → f x = 1) :
  finset.univ.prod f = finset.univ.prod g :=
begin
  by_cases hs : s.nonempty,
  { cases hs with d hd,
    have h : ∀ (fs : finset β), ∃ (fh : β → s),
      (∀ (x : β), x ∈ s → (fh x : s).1 = x) ∧
      fs.prod f = (finset.image fh (fs ∩ s.to_finset)).prod g,
    { rintro fs, apply fs.induction_on; clear fs,
      { fsplit,
        { intro x, apply dite (x ∈ s); intro h,
          { exact ⟨_, h⟩ },
          { exact ⟨_, hd⟩ }},
        { simp, intro x, split_ifs; simp [h] }},
      { rintro x fs h₁ h₂, rcases h₂ with ⟨fh, h₂, h₃⟩, use [fh, h₂],
        rw finset.prod_insert h₁, change _ * fs.prod f = _,
        have hh : ∀ {x y : β}, x ∈ s → y ∈ s → fh x = fh y → x = y,
        { rintro x y hx hy h₄, rw subtype.ext_iff at h₄,
          change (fh x).1 = (fh y).1 at h₄, simp [h₂ _ hx, h₂ _ hy] at h₄,
          exact h₄ },
        by_cases hx : x ∈ s,
        { rw (_ : _ ∩ _ = (insert x (fs ∩ s.to_finset))), swap,
          { apply finset.insert_inter_of_mem, rwa set.mem_to_finset },
          rw [finset.image_insert, finset.prod_insert], swap,
          { intro h₄, rw finset.mem_image at h₄, rcases h₄ with ⟨y, hy, h₄⟩,
            have hy₁ := finset.mem_of_mem_inter_left hy,
            have hy₂ := finset.mem_of_mem_inter_right hy,
            rw set.mem_to_finset at hy₂, replace h₄ := hh hy₂ hx h₄,
            subst h₄, contradiction },
          rw [w _ hx, h₃], congr, ext, simp, exact (h₂ _ hx).symm },
        { rwa [w' _ hx, one_mul, finset.insert_inter_of_not_mem],
          rwa set.mem_to_finset }}},
    obtain ⟨fh, h₁, h₂⟩ := h finset.univ, convert h₂, ext x, simp,
    apply finset.mem_image.mpr, cases x with x hx, simp_rw set.mem_to_finset,
    use [x, hx], ext, simp, exact h₁ _ hx },
  { rw set.not_nonempty_iff_eq_empty at hs, subst s, simp,
    rw finset.prod_eq_one, rintro x hx, apply w', simp },
end