import tactic
import tactic.induction
import logic.function.iterate

noncomputable theory
open_locale classical

def mem_loop {α : Type} (f : α → α) (x : α) (l : list α) : Prop :=
∀ (n : ℕ), l.nth (n % l.length) = some ((f^[n]) x)

def mem_shortest_loop {α : Type} (f : α → α) (x : α) (l : list α) : Prop :=
mem_loop f x l ∧ ∀ (l' : list α), mem_loop f x l' → l.length ≤ l'.length

noncomputable
def mk_finset {α : Type} (f : ℕ → α) : ℕ → finset α
| 0 := ∅
| (n+1) := insert (f n) (mk_finset n)

-----

lemma mk_finset_zero {α : Type} {f : ℕ → α} : mk_finset f 0 = ∅ :=
rfl

lemma mk_finset_succ {α : Type} {f : ℕ → α} {n : ℕ} :
  mk_finset f n.succ = insert (f n) (mk_finset f n) :=
mk_finset.equations._eqn_2 _ _

lemma mem_mk_finset {α : Type} {f : ℕ → α} {n : ℕ} {x : α} :
  x ∈ mk_finset f n ↔ ∃ (i : ℕ), i < n ∧ f i = x :=
begin
  induction n with n ih,
  { rw mk_finset_zero,
    apply iff_of_false (finset.not_mem_empty _),
    push_neg,
    rintro i h,
    cases h },
  { rw [mk_finset_succ, finset.mem_insert],
    split; intro h,
    { cases h,
      { subst h,
        exact ⟨_, lt_add_one _, rfl⟩ },
      { rw ih at h,
        rcases h with ⟨i, h, rfl⟩,
        exact ⟨_, nat.lt_succ_of_lt h, rfl⟩ }},
    { rcases h with ⟨i, h, rfl⟩,
      rw [nat.lt_succ_iff, le_iff_eq_or_lt] at h,
      cases h,
      { left, subst h },
      { right, rw ih, exact ⟨_, h, rfl⟩ }}},
end

lemma iter_add {α : Type} {f : α → α} {x : α} {m n : ℕ} :
  (f^[m + n]) x = (f^[n]) ((f^[m]) x) :=
by rw [add_comm, function.iterate_add_apply]

lemma iter_add_mul_eq_of_add_eq {α : Type}
  {f : α → α} {x : α} {n m d : ℕ}
  (h : (f^[n + d]) x = (f^[n]) x) :
  (f^[n + d * m]) x = (f^[n]) x :=
begin
  induction m with m ih,
  { refl },
  { rwa [nat.mul_succ, ←nat.add_assoc, nat.add_comm n, nat.add_assoc,
    function.iterate_add_apply, h, ←iter_add] },
end

lemma iter_mul_eq_of_eq {α : Type}
  {f : α → α} {x : α} {m d : ℕ}
  (h : (f^[d]) x = x) :
  (f^[d * m]) x = x :=
begin
  rw ←nat.zero_add (d * m),
  apply iter_add_mul_eq_of_add_eq,
  rwa nat.zero_add,
end

lemma list_nth_le_eq_iff {α : Type}
  {l : list α} {n : ℕ} {x : α} {h} :
  l.nth_le n h = x ↔ l.nth n = some x :=
by { rw list.nth_eq_some, tauto }

lemma list_some_nth_le_eq {α : Type}
  {l : list α} {n : ℕ} {h} :
  some (l.nth_le n h) = l.nth n :=
by { symmetry, rw list.nth_eq_some, tauto }

lemma list_nodup_iff {α : Type} {l : list α} :
  l.nodup ↔ ∀ (i j : ℕ), i < j → j < l.length → l.nth i ≠ l.nth j :=
begin
  rw list.nodup_iff_nth_le_inj,
  simp only [list_nth_le_eq_iff, list_some_nth_le_eq],
  split; rintro h i j h₁ h₂,
  { exact mt (h i j (h₁.trans h₂) h₂) (ne_of_lt h₁) },
  { intro h₃,
    by_contra h₄,
    wlog h₅ : i < j,
    { exact ne_iff_lt_or_gt.mp h₄ },
    exact h i j h₅ h₂ h₃ },
end

lemma nat_sub_lt_of_lt {a b c : ℕ} (h : a < b) : a - c < b :=
gt_of_gt_of_ge h (nat.sub_le _ _)

lemma loop_length_pos {α : Type}
  {f : α → α} {x : α} {l : list α}
  (h : mem_loop f x l) :
  0 < l.length :=
begin
  cases l,
  { cases h 0 },
  { dec_trivial },
end

lemma exi_list_func_of_mem_loop {α : Type}
  {f : α → α} {x : α} {l : list α}
  (h : mem_loop f x l) :
  ∃ {g : option α → option α}, ∀ (i : ℕ),
    l.nth (i % l.length) = ((g^[i]) (some x)) :=
begin
  let k := l.length,
  have hk : 0 < k := loop_length_pos h,
  let g : option α → option α,
  { rintro (_ | x),
    { exact none },
    { exact some (f x) }},
  use g,
  rintro i,
  induction i with i ih,
  { exact h 0 },
  { rw [function.iterate_succ_apply', ←ih],
    cases h₁ : l.nth (i % k) with y,
    { rw list.nth_eq_none_iff at h₁,
      contrapose! h₁,
      exact nat.mod_lt _ hk },
    { change _ = some (f y),
      simp_rw [list.nth_eq_some, list_nth_le_eq_iff],
      use [nat.mod_lt _ hk],
      rw [h, option.some.inj_eq] at h₁ ⊢,
      rw [function.iterate_succ_apply', h₁] }},
end

lemma nat_add_sub {a b : ℕ} (h : a ≤ b) : a + (b - a) = b :=
by rw [←nat.add_sub_assoc h, add_tsub_cancel_left]

lemma nat_find_spec_lt {P : ℕ → Prop}
  (h : ∃ (n : ℕ), P n) :
  ∀ (n : ℕ), n < nat.find h → ¬P n :=
λ n h₁, (nat.lt_find_iff h _).mp h₁ n (le_refl _)

lemma nat_mul_add_mod {a b c : ℕ} : (a * b + c) % b = c % b :=
by rw [nat.add_mod, nat.mul_mod, nat.mod_self, nat.mul_zero, nat.zero_mod,
  nat.zero_add, nat.mod_mod]

lemma nat_mul_add_mod_of_lt {a b c : ℕ} (h : c < b) : (a * b + c) % b = c :=
by rw [nat_mul_add_mod, nat.mod_eq_of_lt h]

lemma nat_exi_mul (x y : ℕ) :
  ∃ (a b : ℕ), x / y = a ∧ x % y = b ∧ x = y * a + b :=
⟨_, _, rfl, rfl, (nat.div_add_mod _ _).symm⟩

lemma shortest_loop_nodup {α : Type}
  {f : α → α} {x : α} {l : list α}
  (h : mem_shortest_loop f x l) :
  l.nodup :=
begin
  cases h with hh₁ hh₂,
  let k := l.length,
  have hk : 0 < k := loop_length_pos hh₁,
  obtain ⟨g, hh⟩ := exi_list_func_of_mem_loop hh₁,
  by_contra h₁,
  rw list_nodup_iff at h₁,
  push_neg at h₁,
  let i := nat.find h₁,
  have hi := nat.find_spec h₁,
  change nat.find h₁ with i at hi,
  let j := nat.find hi,
  have hj := nat.find_spec hi,
  change nat.find hi with j at hj,
  rcases hj with ⟨h₂, h₃, h₄⟩,
  change l.length with k at h₃,
  let d := j - i,
  have hd₁ : 0 < d := tsub_pos_of_lt h₂,
  have hd₂ : d < k := nat_sub_lt_of_lt h₃,
  let x' := some x,
  have h₆ := h₂.trans h₃,
  have h₇ := le_of_lt h₆,
  have hi0 : i = 0,
  { by_contra hi₁,
    have h₅ : l.nth 0 = l.nth d,
    { calc l.nth 0 = l.nth ((i + (k - i)) % k) :
          by rw [nat_add_sub h₇, nat.mod_self]
        ... = (g^[i + (k - i)]) x' : by rw hh
        ... = (g^[k - i]) ((g^[i]) x') : by rw iter_add
        ... = (g^[k - i]) (l.nth i) : by rw [←hh, nat.mod_eq_of_lt h₆]
        ... = (g^[k - i]) (l.nth j) : by rw h₄
        ... = (g^[k - i]) ((g^[j]) x') : by rw [←hh, nat.mod_eq_of_lt h₃]
        ... = (g^[j + (k - i)]) x' : by rw iter_add
        ... = l.nth ((j + (k - i)) % k) : by rw hh
        ... = l.nth ((d + k) % k) :
          by rw [←nat.add_sub_assoc h₇, nat.sub_add_comm (le_of_lt h₂)]
        ... = l.nth (d % k) : by rw nat.add_mod_right
        ... = l.nth d : by rw nat.mod_eq_of_lt hd₂ },
    have h₈ := nat_find_spec_lt h₁ _ (nat.pos_of_ne_zero hi₁),
    push_neg at h₈,
    exact h₈ _ hd₁ hd₂ h₅ },
  have hjd : j = d := by { change _ = j - i, rw hi0, refl },
  have hx0 : l.nth 0 = x' := by { rw [←nat.zero_mod k, hh], refl },
  have hxd : l.nth d = x' := by rw [←hx0, ←hjd, ←hi0, h₄],
  have hmd : ∀ (m : ℕ), l.nth ((d * m) % k) = l.nth 0,
  { intro m,
    rw [hh, hx0],
    apply iter_mul_eq_of_eq,
    rwa [←hh, nat.mod_eq_of_lt hd₂] },
  let l' := l.take d,
  have hlen : l'.length = d,
  { rw list.length_take, exact min_eq_left (le_of_lt hd₂) },
  specialize hh₂ l' _,
  { intro m,
    obtain ⟨a, b, ha, hb, hab⟩ := nat_exi_mul m d,
    have hbd : b < d := by { rw ←hb, exact nat.mod_lt _ hd₁ },
    have hbk := hbd.trans hd₂,
    rw [hlen, hb, list.nth_take hbd, ←nat.mod_eq_of_lt hbk, ←hh₁, hab],
    symmetry,
    change l.length with k,
    rw [hh, iter_add, ←hh, hmd, hh, hx0] },
  contrapose! hh₂,
  rwa hlen,
end

lemma exi_mem_shortest_loop_of_mem_loop {α : Type}
  {f : α → α} {x : α} {l : list α}
  (h : mem_loop f x l) :
  ∃ (l' : list α), mem_shortest_loop f x l' :=
begin
  have h₁ : ∃ (n : ℕ) (l : list α), l.length = n ∧ mem_loop f x l,
  { exact ⟨_, _, rfl, h⟩ },
  let n := nat.find h₁,
  obtain ⟨l, h₂, h₃⟩ := nat.find_spec h₁,
  use [l, h₃],
  rintro l' h₄,
  rw h₂,
  by_contra' h₅,
  have h₆ := nat_find_spec_lt h₁ _ h₅,
  push_neg at h₆,
  exact h₆ _ rfl h₄,
end

lemma exi_mem_loop_nodup_of_mem_loop {α : Type}
  {f : α → α} {x : α} {l : list α}
  (h : mem_loop f x l) :
  ∃ (l' : list α), l'.nodup ∧ mem_loop f x l' :=
begin
  obtain ⟨l', h₁⟩ := exi_mem_shortest_loop_of_mem_loop h,
  exact ⟨_, shortest_loop_nodup h₁, h₁.1⟩,
end

lemma list_length_eq_card_to_finset_of_nodup {α : Type} {l : list α}
  (h : l.nodup) : l.length = l.to_finset.card :=
by rw [list.card_to_finset, list.dedup_eq_self.mpr h]

lemma list_length_le_fintype_card_of_nodup {α : Type} [fintype α] {l : list α}
  (h : l.nodup) : l.length ≤ fintype.card α :=
begin
  rw [fintype.card, list_length_eq_card_to_finset_of_nodup h],
  apply finset.card_le_univ,
end

lemma mem_loop_length_le_of_mem_loop {α : Type} [fintype α]
  {f : α → α} {x : α} {l : list α} {n : ℕ}
  (h : mem_loop f x l) :
  ∃ (l' : list α), l'.length ≤ fintype.card α ∧ mem_loop f x l' :=
begin
  obtain ⟨l', h₁, h₂⟩ := exi_mem_loop_nodup_of_mem_loop h,
  exact ⟨_, list_length_le_fintype_card_of_nodup h₁, h₂⟩,
end

lemma card_mk_finset_eq_iff {α : Type}
  {f : α → α} {x : α} {n : ℕ} :
  (mk_finset (λ (i : ℕ), (f^[i]) x) n).card = n ↔
  ∀ (i j : ℕ), i < j → j < n → (f^[i]) x ≠ (f^[j]) x :=
begin
  sorry
end

-- #exit

lemma card_mk_finset_eq_of_iter_add_ne {α : Type}
  {f : α → α} {x : α} {n : ℕ}
  (h : ∀ (m : ℕ), 0 < m → (f^[n + m]) x ≠ (f^[n]) x) :
  (mk_finset (λ (i : ℕ), (f^[i]) x) n).card = n :=
begin
  rw card_mk_finset_eq_iff,
  rintro i j hi hj,
  by_contra' h₁,
  let d := j - i,
  have h₁ : ∀ (m : ℕ), (f^[i + d * m]) x = (f^[i]) x,
  { intro m,
    apply iter_add_mul_eq_of_add_eq,
    change d with j - i,
    rw [nat_add_sub (le_of_lt hi), h₁] },
  have hh := le_of_lt (hi.trans hj),
  obtain ⟨k, hn⟩ := nat.exists_eq_add_of_le hh,
  obtain ⟨a, b, ha, hb, rfl⟩ := nat_exi_mul k d,
  have h₃ : (f^[n]) x = (f^[i + b]) x,
  { rw [hn, ←add_assoc, iter_add, h₁, ←iter_add] },
  have h₄ : (f^[n + d]) x = (f^[i + b]) x,
  { rw [hn, (by linarith : i + (d * a + b) + d = i + d * (a + 1) + b),
    iter_add, h₁, ←iter_add] },
  specialize h d,
  rw [h₃, h₄] at h,
  exact h (tsub_pos_of_lt hi) rfl,
end

lemma exi_iter_add_eq {α : Type} [fintype α]
  {f : α → α} {x : α} {n : ℕ}
  (h : n = fintype.card α) :
  ∃ (m : ℕ), 0 < m ∧ m ≤ n ∧ (f^[n + m]) x = (f^[n]) x :=
begin
  sorry
end

-- #exit

lemma exi_iter_eq {α : Type} [fintype α] :
  ∃ (a b : ℕ), a < b ∧ ∀ {f : α → α}, (f^[a]) = (f^[b]) :=
begin
  let n := fintype.card α,
  use [n, n + n.factorial],
  fsplit,
  { exact lt_add_of_pos_right _ (nat.factorial_pos _) },
  { intro f,
    funext x,
    symmetry,
    obtain ⟨m, hm₁, hm₂, h₁⟩ := @exi_iter_add_eq α _ f x n rfl,
    obtain ⟨a, ha⟩ := nat.dvd_factorial hm₁ hm₂,
    rw [ha, iter_add_mul_eq_of_add_eq h₁] },
end

lemma fin_exi_iter_eq {n : ℕ} :
  ∃ (a b : ℕ), a < b ∧ ∀ {f : fin n → fin n}, (f^[a]) = (f^[b]) :=
exi_iter_eq