import tactic
import tactic.induction
import data.pnat.basic
import data.nat.lattice
import order.complete_lattice

-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/proof.20tactics.20suggestion
-- https://artofproblemsolving.com/wiki/index.php/1977_IMO_Problems/Problem_6

constant a : unit

lemma pnat_ind {P : ℕ+ → Prop} {n : ℕ+}
  (h₁ : P 1) (h₂ : ∀ (n : ℕ+), P n → P (n + 1)) : P n :=
begin
  cases n with n hn, obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_lt hn,
  simp_rw nat.zero_add, generalize_proofs hn₁, clear hn, induction' n,
  { exact h₁ },
  { exact h₂ ⟨n + 1, nat.zero_lt_succ _⟩ (@ih P h₁ h₂ (nat.zero_lt_succ _)) },
end

lemma pnat_strong_ind {P : ℕ+ → Prop} {n : ℕ+}
  (h₂ : ∀ (n : ℕ+), (∀ (k < n), P k) → P n) : P n :=
begin
  cases n with n hn, obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_lt hn,
  simp_rw nat.zero_add, generalize_proofs hn₁, clear hn,
  induction n using nat.strong_induction_on with n ih,
  apply h₂, rintro k h₃, cases k with k hk,
  obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_lt hk,
  simp_rw nat.zero_add at h₃ ⊢, apply ih, simp at h₃, exact h₃,
end

lemma pnat_strong_ind' {P : ℕ+ → Prop} {n : ℕ+}
  (h₁ : P 1)
  (h₂ : ∀ (n : ℕ+), (∀ (k ≤ n), P k) → P (n + 1)) : P n :=
begin
  apply pnat_strong_ind,
  rintro n h₃,
  cases n with n hn, obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_lt hn,
  simp_rw nat.zero_add,
  cases n with n,
  {
    exact h₁,
  },
  {
    change P (⟨n + 1, nat.zero_lt_succ _⟩ + 1),
    apply h₂,
    simp_rw nat.zero_add at h₃,
    rintro k hk,
    specialize h₃ k,
    apply h₃,
    cases k with k hk₁, obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_lt hk₁, clear h₃,
    simp at hk ⊢,
    exact nat.lt_succ_iff.mpr hk,
  },
end

def seq_a (f : ℕ+ → ℕ+) (z : ℕ+) : ℕ → option ℕ+
| 0 := some z
| (nat.succ i) := match seq_a i with
  | none := none
  | (some n) := if n = 1 then none else f (n - 1)
end

lemma pnat_add_sub {a b : ℕ+} : a + b - b = a :=
begin
  cases a with a ha, cases b with b hb, change (_ : ℕ).to_pnat' = _, simp,
  rw nat.to_pnat', obtain ⟨a, rfl⟩ := nat.exists_eq_add_of_lt ha, simp, congr,
end

theorem imo_1977_p6
  (f : ℕ+ → ℕ+)
  (h : ∀ n, f (f n) < f (n + 1)) :
  ∀ n, f n = n :=
begin
  intro n,
  induction n using pnat_strong_ind' with n ih,
  {
    have h₁ : ∃ (n : ℕ+), 1 < n,
    { exact ⟨2, dec_trivial⟩ },
    let a₀ := h₁.some,
    let a := seq_a f a₀,
    have h₂ : ∀ i n n₁, a i = some n → a (i + 1) = some n₁ → f n₁ < f n,
    {
      admit
      -- rintro i n n₁ h₂ h₃,
      -- change seq_a _ _ _ = _ at h₃,
      -- have h₄ : seq_a _ _ _ = _ := h₂,
      -- unfold seq_a at h₃,
      -- rw h₄ at h₃, clear h₄,
      -- unfold seq_a at h₃,
      -- split_ifs at h₃ with h₄, { cases h₃ },
      -- replace h₃ : n₁ = f (n - 1),
      -- { cases h₃, refl },
      -- subst h₃,
      -- obtain ⟨n, rfl⟩ := pnat.exists_eq_succ_of_ne_one h₄,
      -- rw pnat_add_sub,
      -- apply h,
    },
    have h₃ : ∀ (i : ℕ), (a i.succ).is_some → (a i).is_some,
    sorry,
    have h₄ : ∃ (i : ℕ), a i = none,
    {
      admit
      -- use a₀,
      -- have h₄ : ∀ (i n : ℕ+), a i = some n → n + i ≤ a₀,
      -- {
      --   sorry
      -- },
      -- specialize h₄ a₀,
      -- rw ←option.not_is_some_iff_eq_none,
      -- by_contra' h₅,
      -- rw option.is_some_iff_exists at h₅,
      -- cases h₅ with n hn,
      -- specialize h₄ n hn,
      -- contrapose! h₄,
      -- apply pnat.lt_add_left,
    },
    let i := nat.find h₄,
    admit
  },
  {
    dsimp at ih,
    admit
  },
end

-- example {a b : ℕ}
--   (h₁ : a ≤ b)
--   (h₂ : b ≤ a) :
--   a = b :=
-- begin
--   library_search,
-- end