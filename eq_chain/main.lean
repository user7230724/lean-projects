import tactic
import tactic.induction

noncomputable theory
open_locale classical

def eq₁ {α : Sort*} (s : list α) : Prop := ∀ (x y ∈ s), x = y

def eq₂ {α : Sort*} : list α → Prop
| [] := true
| [x] := true
| [x, y] := x = y
| (x :: y :: z :: rest) :=
  list.foldr (∧) (eq₂ (y :: z :: rest)) (list.map ((=) x) (y :: z :: rest))

lemma eq_of_eq_cons {α : Sort*} {s : list α} {x : α}
  (h : eq₁ (x :: s)) : eq₁ s :=
λ a ha b hb, h a (by simp [ha]) b (by simp [hb])

lemma foldr_true {s : list Prop} :
  list.foldr and true s ↔ ∀ (P ∈ s), P :=
begin
  induction' s, { simp }, rw list.foldr, split; intro h,
  { rintro P h₁, cases h₁, { rw h₁, exact h.1 }, { apply ih.mp h.2 P h₁ } },
  { split, { apply h, simp }, { apply ih.mpr, rintro P h₁, apply h, simp [h₁] }},
end

lemma list_mem_cons_dup {α : Sort*} {s : list α} {x hd : α} :
  x ∈ (hd :: hd :: s) ↔ x ∈ (hd :: s) :=
by simp [list.mem_cons_iff]

lemma eq_cons_dup {α : Sort*} {s : list α} {hd : α} :
  eq₁ (hd :: hd :: s) ↔ eq₁ (hd :: s) :=
by simp [eq₁, list_mem_cons_dup]

lemma foldr_true_z {s : list Prop} {P : Prop}
  (h : list.foldr and P s) : P :=
by { induction' s, { exact h }, { exact ih h.2 }}

lemma eq_aux {α : Sort*} {s : list α} {x : α} :
  eq₁ (x :: s) ↔ list.foldr and (eq₁ s) (list.map (eq x) s) :=
begin
  induction' s, { simp [eq₁] },
  rw [list.map_cons, list.foldr_cons], split; intro h,
  { use h x (by simp) hd (by simp), have h₁ := eq_of_eq_cons h,
    have h₂ := eq_of_eq_cons h₁, have h₃ := ih.mp h₁,
    rw iff_of_true h₂ trivial at h₃, rw iff_of_true h₁ trivial,
    rw foldr_true at h₃ ⊢, rintro P hP, apply h₃,
    rw list.mem_map at hP ⊢, rcases hP with ⟨y, hy, rfl⟩,
    use [y, hy], ext, split; rintro rfl,
    { exact h x (by simp) hd (by simp) },
    { exact h hd (by simp) x (by simp) }},
  { rcases h with ⟨rfl, h⟩, rw eq_cons_dup, apply ih.mpr,
    have h₁ := foldr_true_z h, have h₂ := eq_of_eq_cons h₁,
    rw iff_of_true h₁ trivial at h, rwa iff_of_true h₂ trivial },
end

example {α : Sort*} {s : list α} : eq₁ s ↔ eq₂ s :=
begin
  induction' s, { simp [eq₁, eq₂] },
  cases' s with x s, { simp [eq₁, eq₂], },
  cases' s with y s, { simp [eq₁, eq₂], exact λ h, h.symm },
  rw eq₂, simp_rw ←ih, clear ih, exact eq_aux,
end