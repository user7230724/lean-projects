import tactic
import tactic.induction
import data.int.basic
import data.set.basic

import .base .point .dist .board .state

noncomputable theory
open_locale classical

instance {b : Board} : inhabited (Valid_D_move b) :=
⟨⟨none, trivial⟩⟩

-----

instance {pw : ℕ} : inhabited (A pw) :=
⟨⟨λ s hs h, ⟨h.some, h.some_spec⟩⟩⟩

instance : inhabited D :=
⟨⟨λ s hs, ⟨none, trivial⟩⟩⟩

def A.sup {pw pw₁ : ℕ} (a₁ : A pw₁) (a : A pw) : Prop :=
∀ s hs h, ∃ hs₁ h₁, (a₁.f s hs₁ h₁).m = (a.f s hs h).m

def A.sub {pw₁ pw : ℕ} (a : A pw₁) (a₁ : A pw) : Prop :=
a₁.sup a

def A_prev_moves (pw : ℕ) (s : State) :=
Π (s₁ : State), s₁.act → s₁.len < s.len →
A_has_valid_move pw s₁.board → Valid_A_move pw s₁.board

def D_prev_moves (s : State) :=
Π (s₁ : State), s₁.act → s₁.len < s.len →
Valid_D_move s₁.board

def A.set_prev_moves {pw : ℕ} (a : A pw) (s : State)
  (pm : A_prev_moves pw s) : A pw :=
begin
  refine ⟨λ s₁ hs h₁, _⟩,
  apply dite (s₁.len < s.len); intro h₂,
  { exact pm s₁ hs h₂ h₁ },
  { exact a.f s₁ hs h₁ },
end

def D.set_prev_moves (d : D) (s : State)
  (pm : D_prev_moves s) : D :=
begin
  refine ⟨λ s₁ hs, _⟩,
  apply dite (s₁.len < s.len); intro h₁,
  { exact pm s₁ hs h₁ },
  { exact d.f s₁ hs },
end

def A.set_move {pw : ℕ} (a : A pw) (s : State)
  (ma : Valid_A_move pw s.board) : A pw :=
begin
  refine ⟨λ s₁ hs h, _⟩, apply dite (s₁ = s); intro h₁,
  { cases h₁, exact ma },
  { exact a.f s₁ hs h },
end

def D.set_move (d : D) (s : State)
  (md : Valid_D_move s.board) : D :=
begin
  refine ⟨λ s₁ hs, _⟩, apply dite (s₁ = s); intro h₁,
  { cases h₁, exact md },
  { exact d.f s₁ hs },
end

def A.prev_moves_id {pw : ℕ} (a : A pw) (s : State) : A pw :=
a.set_prev_moves s (λ s₁ hs _ h, a.f s₁ hs h)

def D.prev_moves_id (d : D) (s : State) : D :=
d.set_prev_moves s (λ s₁ hs h, d.f s₁ hs)

def A.prev_moves_set {pw : ℕ} (a : A pw) (s : State)
  (s₁ : State) (m : Valid_A_move pw s₁.board)
  (h : s₁.len < s.len) : A pw :=
begin
  apply a.set_prev_moves s, rintro s₂ hs h₁ h₂,
  apply dite (s₂ = s₁); intro h₃,
  { cases h₃, exact m },
  { exact a.f s₂ hs h₂ },
end

def D.prev_moves_set (d : D) (s : State)
  (s₁ : State) (m : Valid_D_move s₁.board)
  (h : s₁.len < s.len) : D :=
begin
  apply d.set_prev_moves s, rintro s₂ hs h₁,
  apply dite (s₂ = s₁); intro h₂,
  { cases h₂, exact m },
  { exact d.f s₂ hs },
end

def A_state (s : State) : Prop := odd s.len
def D_state (s : State) : Prop := even s.len

-----

lemma A_move_valid_ge_of {pw pw₁ : ℕ} {b : Board} {p : A_move}
  (h₁ : pw ≤ pw₁) (h₂ : A_move_valid pw b p) :
  A_move_valid pw₁ b p :=
⟨h₂.1, h₂.2.1.trans h₁, h₂.2.2⟩

lemma A_has_valid_move_ge_of {pw pw₁ : ℕ} {b : Board}
  (h₁ : pw ≤ pw₁) (h₂ : A_has_valid_move pw b) :
  A_has_valid_move pw₁ b :=
by { cases h₂ with m h₂, use m, exact A_move_valid_ge_of h₁ h₂ }

lemma As_eq_iff {pw : ℕ} {a₁ a₂ : A pw} :
  a₁ = a₂ ↔ ∀ s hs h, a₁.f s hs h = a₂.f s hs h :=
begin
  split; intro h,
  { subst h, simp },
  { cases a₁ with f₁, cases a₂ with f₂, congr, ext, apply h },
end

lemma Ds_eq_iff {d₁ d₂ : D} :
  d₁ = d₂ ↔ ∀ s hs, d₁.f s hs = d₂.f s hs :=
begin
  split; intro h,
  { subst h, simp },
  { cases d₁ with f₁, cases d₂ with f₂, congr, ext, apply h },
end

lemma A_prev_moves_id_eq {pw : ℕ} {a : A pw} {s : State} :
  a.prev_moves_id s = a :=
by { rw As_eq_iff, rintro s₁ hs h, change dite _ _ _ = _, split_ifs; refl }

lemma D_prev_moves_id_eq {d : D} {s : State} :
  d.prev_moves_id s = d :=
by { rw Ds_eq_iff, rintro s₁ hs, change dite _ _ _ = _, split_ifs; refl }

lemma A_set_move_eq {pw : ℕ} {a : A pw}
  {s : State} {m : Valid_A_move pw s.board} {hs h} :
  (a.set_move s m).f s hs h = m :=
by { change dite _ _ _ = _, split_ifs with h₁; refl }

lemma D_set_move_eq {d : D}
  {s : State} {m : Valid_D_move s.board} {hs} :
  (d.set_move s m).f s hs = m :=
by { change dite _ _ _ = _, split_ifs with h₁; refl }

lemma A_set_move_self {pw : ℕ} {a : A pw}
  {s : State} {hs h} : a.set_move s (a.f s hs h) = a :=
begin
  rw As_eq_iff; intros, change dite _ _ _ = _, split_ifs with h₂,
  { subst h₂ }, { refl },
end

lemma D_set_move_self {d : D}
  {s : State} {hs} : d.set_move s (d.f s hs) = d :=
begin
  rw Ds_eq_iff; intros, change dite _ _ _ = _, split_ifs with h₂,
  { subst h₂ }, { refl },
end

lemma A_set_move_set_move_eq {pw : ℕ} {a : A pw} {s : State}
  {m₁ m₂ : Valid_A_move pw s.board} :
  (a.set_move s m₁).set_move s m₂ = a.set_move s m₂ :=
begin
  rw As_eq_iff, rintro s₁ hs h₁,
  change dite _ _ _ = _, split_ifs with h₂,
  { subst h₂, rw A_set_move_eq },
  { change dite _ _ _ = dite _ _ _, simp_rw dif_neg h₂ },
end

lemma D_set_move_set_move_eq {d : D} {s : State}
  {m₁ m₂ : Valid_D_move s.board} :
  (d.set_move s m₁).set_move s m₂ = d.set_move s m₂ :=
begin
  rw Ds_eq_iff, rintro s₁ hs,
  change dite _ _ _ = _, split_ifs with h₂,
  { subst h₂, rw D_set_move_eq },
  { change dite _ _ _ = dite _ _ _, simp_rw dif_neg h₂ },
end

lemma A_prev_moves_set_eq {pw : ℕ} {a : A pw} {s s₁ : State}
  {m : Valid_A_move pw s₁.board} {h} :
  a.prev_moves_set s s₁ m h = a.set_move s₁ m :=
begin
  rw As_eq_iff, rintro s₂ hs h,
  change dite _ _ _ = _, split_ifs with h₁,
  { dsimp, split_ifs with h₂,
    { subst h₂, simp [A_set_move_eq] },
    { change _ = dite _ _ _, rw dif_neg h₂ }},
  { change _ = dite _ _ _, split_ifs with h₂,
    { subst h₂, contradiction },
    { refl }},
end

lemma D_prev_moves_set_eq {d : D} {s s₁ : State}
  {m : Valid_D_move s₁.board} {h} :
  d.prev_moves_set s s₁ m h = d.set_move s₁ m :=
begin
  rw Ds_eq_iff, rintro s₂ hs,
  change dite _ _ _ = _, split_ifs with h₁,
  { dsimp, split_ifs with h₂,
    { subst h₂, simp [D_set_move_eq] },
    { change _ = dite _ _ _, rw dif_neg h₂ }},
  { change _ = dite _ _ _, split_ifs with h₂,
    { subst h₂, contradiction },
    { refl }},
end

lemma hist_len_apply_move {s : State} {b : Board} :
  (apply_move s b).len = s.len.succ :=
by { change (_ ++ [_]).length = _, rw list.length_append, refl }

lemma hist_len_apply_A_move {s : State} {ma : A_move} :
  (apply_A_move s ma).len = s.len.succ :=
hist_len_apply_move

lemma hist_len_apply_D_move {s : State} {md : D_move} :
  (apply_D_move s md).len = s.len.succ :=
hist_len_apply_move

lemma valid_A_move_ext {pw : ℕ} {b : Board}
  {ma₁ ma₂ : Valid_A_move pw b}
  (h : ma₁.m = ma₂.m) : ma₁ = ma₂ :=
by { cases ma₁, cases ma₂, congr, exact h }

lemma valid_D_move_ext {b : Board}
  {md₁ md₂ : Valid_D_move b}
  (h : md₁.m = md₂.m) : md₁ = md₂ :=
by { cases md₁, cases md₂, congr, exact h }

lemma A_moves_eq_iff' {pw : ℕ} {s : State}
  {ma₁ ma₂ : Valid_A_move pw s.board} : ma₁ = ma₂ ↔
  (apply_A_move s ma₁.m).board = (apply_A_move s ma₂.m).board :=
begin
  split; intro h, { rw h }, simp_rw [apply_A_move, apply_A_move_b, apply_move] at h,
  cases h with h₁ h₂, cases ma₁, cases ma₂, simp at h₂ ⊢, exact h₂,
end

lemma D_moves_eq_iff' {s : State}
  {md₁ md₂ : Valid_D_move s.board} : md₁ = md₂ ↔
  (apply_D_move s md₁.m).board = (apply_D_move s md₂.m).board :=
begin
  split; intro h, { rw h }, simp_rw [apply_D_move, apply_move] at h,
  cases md₁ with m₁ h₁, cases md₂ with m₂ h₂,
  apply valid_D_move_ext, dsimp at h ⊢,
  cases m₁ with p₁; cases m₂ with p₂; simp_rw apply_D_move_b at h,
  { cases h₂ with h₂ h₃, contrapose! h₃, rw h, simp },
  { cases h₁ with h₁ h₃, contrapose! h₃, rw ←h, simp },
  { replace h := h.1, replace h₁ := h₁.2, replace h₂ := h₂.2, congr,
    rw set.ext_iff at h, have h₃ := h p₁, simp at h₃, exact h₃ h₁ },
end

lemma A_moves_eq_iff {pw : ℕ} {s : State}
  {ma₁ ma₂ : Valid_A_move pw s.board} :
  ma₁ = ma₂ ↔ apply_A_move s ma₁.m = apply_A_move s ma₂.m :=
begin
  split; intro h, { rw h }, simp_rw [apply_A_move, apply_A_move_b, apply_move] at h,
  exact valid_A_move_ext h.1.2,
end

lemma D_moves_eq_iff {s : State}
  {md₁ md₂ : Valid_D_move s.board} :
  md₁ = md₂ ↔ apply_D_move s md₁.m = apply_D_move s md₂.m :=
begin
  split; intro h, { rw h }, simp_rw [apply_D_move, apply_move] at h,
  replace h := h.1, cases md₁ with m₁ h₁, cases md₂ with m₂ h₂,
  apply valid_D_move_ext, dsimp at h ⊢,
  cases m₁ with p₁; cases m₂ with p₂; simp_rw apply_D_move_b at h,
  { cases h₂ with h₂ h₃, contrapose! h₃, rw h, simp },
  { cases h₁ with h₁ h₃, contrapose! h₃, rw ←h, simp },
  { replace h := h.1, replace h₁ := h₁.2, replace h₂ := h₂.2, congr,
    rw set.ext_iff at h, have h₃ := h p₁, simp at h₃, exact h₃ h₁ },
end

lemma A_set_move_eq_pos {pw : ℕ} {a : A pw} {s : State}
  {ma : Valid_A_move pw s.board} {hs h} :
  (a.set_move s ma).f s hs h = ma :=
by { rw A.set_move, dsimp, split_ifs; refl }

lemma D_set_move_eq_pos {d : D} {s : State}
  {md : Valid_D_move s.board} {hs} :
  (d.set_move s md).f s hs = md :=
by { rw D.set_move, dsimp, split_ifs; refl }

lemma state_eq_of_apply_A_move_eq {s₁ s₂ : State}
  {ma₁ ma₂ : A_move}
  (h : apply_A_move s₁ ma₁ = apply_A_move s₂ ma₂) :
  s₁ = s₂ :=
begin
  cases s₁ with b₁ t₁ a₁, cases s₂ with b₂ t₂ a₂,
  simp_rw [apply_A_move, apply_A_move_b, apply_move] at h, simp only,
  rcases h with ⟨⟨h₁, h₂⟩, h₃, h₄⟩, rw snoc_eq_snoc_iff at h₃, cc,
end

lemma state_eq_of_apply_D_move_eq {s₁ s₂ : State}
  {ma₁ ma₂ : D_move}
  (h : apply_D_move s₁ ma₁ = apply_D_move s₂ ma₂) :
  s₁ = s₂ :=
begin
  cases s₁ with b₁ t₁ a₁, cases s₂ with b₂ t₂ a₂,
  cases ma₁ with p₁; cases ma₂ with p₂;
  simp_rw [apply_D_move, apply_D_move_b, apply_move, snoc_eq_snoc_iff] at h;
  simp only; tauto!,
end

lemma apply_move_state_nth_eq_some_of {n : ℕ} {s : State} {b sb : Board}
  (h : s.nth n = some sb) :
  (apply_move s b).nth n = some sb :=
begin
  simp_rw [State.nth, apply_move] at h ⊢, rw list.nth_append,
  { exact h },
  { rw [length_snoc, nat.lt_succ_iff], obtain ⟨h₁, h₂⟩ := list.nth_eq_some.mp h,
    rw length_snoc at h₁, exact nat.lt_succ_iff.mp h₁ },
end

lemma apply_A_move_state_nth_eq_some_of {n : ℕ}
  {s : State} {ma : A_move} {b : Board}
  (h : s.nth n = some b) :
  (apply_A_move s ma).nth n = some b :=
apply_move_state_nth_eq_some_of h

lemma apply_D_move_state_nth_eq_some_of {n : ℕ}
  {s : State} {ma : D_move} {b : Board}
  (h : s.nth n = some b) :
  (apply_D_move s ma).nth n = some b :=
apply_move_state_nth_eq_some_of h

lemma apply_move_len {s : State} {b : Board} :
  (apply_move s b).len = s.len.succ :=
length_snoc

lemma apply_A_move_len {s : State} {ma : A_move} :
  (apply_A_move s ma).len = s.len.succ :=
apply_move_len

lemma apply_D_move_len {s : State} {ma : D_move} :
  (apply_D_move s ma).len = s.len.succ :=
apply_move_len

lemma apply_D_move_A_eq {b : Board} {md : Valid_D_move b} :
  (apply_D_move_b b md.m).A = b.A :=
by { rcases md with ⟨_ | md, h⟩; refl }

-----

def Valid_A_move_subtype (pw : ℕ) (b : Board) :=
{m : A_move // A_move_valid pw b m}

def Valid_D_move_subtype (b : Board) :=
{m : D_move // D_move_valid b m}

def Valid_A_move_equiv_subtype {pw : ℕ} {b : Board} :
  Valid_A_move pw b ≃ Valid_A_move_subtype pw b :=
begin
  fapply equiv.of_bijective, { intro ma, exact ⟨_, ma.h⟩ }, fsplit,
  { rintro ⟨m₁, h₁⟩ ⟨m2, h₂⟩ h₃, congr, exact subtype.mk.inj h₃ },
  { rintro ⟨m, h⟩, use ⟨_, h⟩ },
end

def Valid_D_move_equiv_subtype {b : Board} :
  Valid_D_move b ≃ Valid_D_move_subtype b :=
begin
  fapply equiv.of_bijective, { intro ma, exact ⟨_, ma.h⟩ }, fsplit,
  { rintro ⟨m₁, h₁⟩ ⟨m2, h₂⟩ h₃, congr, exact subtype.mk.inj h₃ },
  { rintro ⟨m, h⟩, use ⟨_, h⟩ },
end

-----

instance {pw : ℕ} {b : Board} : fintype (Valid_A_move_subtype pw b) :=
begin
  apply fintype_subtype_of_set_finite, apply set.finite.inter_of_right,
  apply set.finite.inter_of_left, change {p : Point | dist p b.A ≤ pw}.finite,
  exact dist_le_set_finite,
end

instance {pw : ℕ} {b : Board} : fintype (Valid_A_move pw b) :=
fintype.of_equiv _ Valid_A_move_equiv_subtype.symm

-----

lemma Valid_A_move_eq_iff {pw : ℕ} {b : Board}
  {ma₁ ma₂ : Valid_A_move pw b} :
  ma₁ = ma₂ ↔ ma₁.m = ma₂.m :=
by { cases ma₁, cases ma₂, simp }

lemma Valid_D_move_eq_iff {pw : ℕ} {b : Board}
  {md₁ md₂ : Valid_A_move pw b} :
  md₁ = md₂ ↔ md₁.m = md₂.m :=
by { cases md₁, cases md₂, simp }