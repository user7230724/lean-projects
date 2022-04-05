import tactic
import tactic.induction
import data.int.basic
import data.set.basic

import .util .point .dist .board .state

noncomputable theory
open_locale classical

def Angel_move : Type := Point
def Devil_move : Type := option Point

def angel_move_valid (pw : ℕ) (b : Board) (p : Angel_move) : Prop :=
p ≠ b.angel ∧ dist p b.angel ≤ pw ∧ p ∈ b.squares

def devil_move_valid (b : Board) : Devil_move → Prop
| (option.none) := true
| (option.some p) := p ≠ b.angel ∧ p ∈ b.squares

def angel_has_valid_move (pw : ℕ) (b : Board) :=
∃ (m : Angel_move), angel_move_valid pw b m

structure Valid_angel_move (pw : ℕ) (b : Board) :=
(m : Angel_move)
(h : angel_move_valid pw b m)

structure Valid_devil_move (b : Board) :=
(m : Devil_move)
(h : devil_move_valid b m)

instance {b : Board} : inhabited (Valid_devil_move b) :=
⟨⟨none, trivial⟩⟩

def apply_move (s : State) (b : Board) : State :=
{s with board := b, history := s.history ++ [s.board] }

def apply_angel_move (s : State) (p : Angel_move) : State :=
apply_move s {s.board with angel := p}

def apply_devil_move' (s : State) : Devil_move → Board
| (option.none) := s.board
| (option.some p) := {s.board with squares := s.board.squares \ {p}}

def apply_devil_move (s : State) (m : Devil_move) : State :=
apply_move s (apply_devil_move' s m)

-----

structure Angel (pw : ℕ) : Type :=
(f : Π (s : State), s.act →
  angel_has_valid_move pw s.board → Valid_angel_move pw s.board)

structure Devil : Type :=
(f : Π (s : State), s.act → Valid_devil_move s.board)

instance {pw : ℕ} : inhabited (Angel pw) :=
⟨⟨λ s hs h, ⟨h.some, h.some_spec⟩⟩⟩

instance : inhabited Devil :=
⟨⟨λ s hs, ⟨none, trivial⟩⟩⟩

def Angel.sup {pw pw₁ : ℕ} (a₁ : Angel pw₁) (a : Angel pw) : Prop :=
∀ s hs h, ∃ hs₁ h₁, (a₁.f s hs₁ h₁).m = (a.f s hs h).m

def Angel.sub {pw₁ pw : ℕ} (a : Angel pw₁) (a₁ : Angel pw) : Prop :=
a₁.sup a

def Angel_prev_moves (pw : ℕ) (s : State) :=
Π (s₁ : State), s₁.act → s₁.history.length < s.history.length →
angel_has_valid_move pw s₁.board → Valid_angel_move pw s₁.board

def Devil_prev_moves (s : State) :=
Π (s₁ : State), s₁.act → s₁.history.length < s.history.length →
Valid_devil_move s₁.board

def Angel.set_prev_moves {pw : ℕ} (a : Angel pw) (s : State)
  (pm : Angel_prev_moves pw s) : Angel pw :=
begin
  refine ⟨λ s₁ hs h₁, _⟩,
  apply dite (s₁.history.length < s.history.length); intro h₂,
  { exact pm s₁ hs h₂ h₁ },
  { exact a.f s₁ hs h₁ },
end

def Devil.set_prev_moves (d : Devil) (s : State)
  (pm : Devil_prev_moves s) : Devil :=
begin
  refine ⟨λ s₁ hs, _⟩,
  apply dite (s₁.history.length < s.history.length); intro h₁,
  { exact pm s₁ hs h₁ },
  { exact d.f s₁ hs },
end

def Angel.set_move {pw : ℕ} (a : Angel pw) (s : State)
  (ma : Valid_angel_move pw s.board) : Angel pw :=
begin
  refine ⟨λ s₁ hs h, _⟩, apply dite (s₁ = s); intro h₁,
  { cases h₁, exact ma },
  { exact a.f s₁ hs h },
end

def Devil.set_move (d : Devil) (s : State)
  (md : Valid_devil_move s.board) : Devil :=
begin
  refine ⟨λ s₁ hs, _⟩, apply dite (s₁ = s); intro h₁,
  { cases h₁, exact md },
  { exact d.f s₁ hs },
end

def Angel.prev_moves_id {pw : ℕ} (a : Angel pw) (s : State) : Angel pw :=
a.set_prev_moves s (λ s₁ hs _ h, a.f s₁ hs h)

def Devil.prev_moves_id (d : Devil) (s : State) : Devil :=
d.set_prev_moves s (λ s₁ hs h, d.f s₁ hs)

def Angel.prev_moves_set {pw : ℕ} (a : Angel pw) (s : State)
  (s₁ : State) (m : Valid_angel_move pw s₁.board)
  (h : s₁.history.length < s.history.length) : Angel pw :=
begin
  apply a.set_prev_moves s, rintro s₂ hs h₁ h₂,
  apply dite (s₂ = s₁); intro h₃,
  { cases h₃, exact m },
  { exact a.f s₂ hs h₂ },
end

def Devil.prev_moves_set (d : Devil) (s : State)
  (s₁ : State) (m : Valid_devil_move s₁.board)
  (h : s₁.history.length < s.history.length) : Devil :=
begin
  apply d.set_prev_moves s, rintro s₂ hs h₁,
  apply dite (s₂ = s₁); intro h₂,
  { cases h₂, exact m },
  { exact d.f s₂ hs },
end

def angel_state (s : State) : Prop := odd s.history.length
def devil_state (s : State) : Prop := even s.history.length

-----

lemma angel_move_valid_ge_of {pw pw₁ : ℕ} {b : Board} {p : Angel_move}
  (h₁ : pw ≤ pw₁) (h₂ : angel_move_valid pw b p) :
  angel_move_valid pw₁ b p :=
⟨h₂.1, h₂.2.1.trans h₁, h₂.2.2⟩

lemma angel_has_valid_move_ge_of {pw pw₁ : ℕ} {b : Board}
  (h₁ : pw ≤ pw₁) (h₂ : angel_has_valid_move pw b) :
  angel_has_valid_move pw₁ b :=
by { cases h₂ with m h₂, use m, exact angel_move_valid_ge_of h₁ h₂ }

lemma angels_eq_iff {pw : ℕ} {a₁ a₂ : Angel pw} :
  a₁ = a₂ ↔ ∀ s hs h, a₁.f s hs h = a₂.f s hs h :=
begin
  split; intro h,
  { subst h, simp },
  { cases a₁ with f₁, cases a₂ with f₂, congr, ext, apply h },
end

lemma devils_eq_iff {d₁ d₂ : Devil} :
  d₁ = d₂ ↔ ∀ s hs, d₁.f s hs = d₂.f s hs :=
begin
  split; intro h,
  { subst h, simp },
  { cases d₁ with f₁, cases d₂ with f₂, congr, ext, apply h },
end

lemma angel_prev_moves_id_eq {pw : ℕ} {a : Angel pw} {s : State} :
  a.prev_moves_id s = a :=
by { rw angels_eq_iff, rintro s₁ hs h, change dite _ _ _ = _, split_ifs; refl }

lemma devil_prev_moves_id_eq {d : Devil} {s : State} :
  d.prev_moves_id s = d :=
by { rw devils_eq_iff, rintro s₁ hs, change dite _ _ _ = _, split_ifs; refl }

lemma angel_set_move_eq {pw : ℕ} {a : Angel pw}
  {s : State} {m : Valid_angel_move pw s.board} {hs h} :
  (a.set_move s m).f s hs h = m :=
by { change dite _ _ _ = _, split_ifs with h₁; refl }

lemma devil_set_move_eq {d : Devil}
  {s : State} {m : Valid_devil_move s.board} {hs} :
  (d.set_move s m).f s hs = m :=
by { change dite _ _ _ = _, split_ifs with h₁; refl }

lemma angel_set_move_self {pw : ℕ} {a : Angel pw}
  {s : State} {hs h} : a.set_move s (a.f s hs h) = a :=
begin
  rw angels_eq_iff; intros, change dite _ _ _ = _, split_ifs with h₂,
  { subst h₂ }, { refl },
end

lemma devil_set_move_self {d : Devil}
  {s : State} {hs} : d.set_move s (d.f s hs) = d :=
begin
  rw devils_eq_iff; intros, change dite _ _ _ = _, split_ifs with h₂,
  { subst h₂ }, { refl },
end

lemma angel_set_move_set_move_eq {pw : ℕ} {a : Angel pw} {s : State}
  {m₁ m₂ : Valid_angel_move pw s.board} :
  (a.set_move s m₁).set_move s m₂ = a.set_move s m₂ :=
begin
  rw angels_eq_iff, rintro s₁ hs h₁,
  change dite _ _ _ = _, split_ifs with h₂,
  { subst h₂, rw angel_set_move_eq },
  { change dite _ _ _ = dite _ _ _, simp_rw dif_neg h₂ },
end

lemma devil_set_move_set_move_eq {d : Devil} {s : State}
  {m₁ m₂ : Valid_devil_move s.board} :
  (d.set_move s m₁).set_move s m₂ = d.set_move s m₂ :=
begin
  rw devils_eq_iff, rintro s₁ hs,
  change dite _ _ _ = _, split_ifs with h₂,
  { subst h₂, rw devil_set_move_eq },
  { change dite _ _ _ = dite _ _ _, simp_rw dif_neg h₂ },
end

lemma angel_prev_moves_set_eq {pw : ℕ} {a : Angel pw} {s s₁ : State}
  {m : Valid_angel_move pw s₁.board} {h} :
  a.prev_moves_set s s₁ m h = a.set_move s₁ m :=
begin
  rw angels_eq_iff, rintro s₂ hs h,
  change dite _ _ _ = _, split_ifs with h₁,
  { dsimp, split_ifs with h₂,
    { subst h₂, simp [angel_set_move_eq] },
    { change _ = dite _ _ _, rw dif_neg h₂ }},
  { change _ = dite _ _ _, split_ifs with h₂,
    { subst h₂, contradiction },
    { refl }},
end

lemma devil_prev_moves_set_eq {d : Devil} {s s₁ : State}
  {m : Valid_devil_move s₁.board} {h} :
  d.prev_moves_set s s₁ m h = d.set_move s₁ m :=
begin
  rw devils_eq_iff, rintro s₂ hs,
  change dite _ _ _ = _, split_ifs with h₁,
  { dsimp, split_ifs with h₂,
    { subst h₂, simp [devil_set_move_eq] },
    { change _ = dite _ _ _, rw dif_neg h₂ }},
  { change _ = dite _ _ _, split_ifs with h₂,
    { subst h₂, contradiction },
    { refl }},
end

lemma hist_len_apply_move {s : State} {b : Board} :
  (apply_move s b).history.length = s.history.length.succ :=
by { change (_ ++ [_]).length = _, rw list.length_append, refl }

lemma hist_len_apply_angel_move {s : State} {ma : Angel_move} :
  (apply_angel_move s ma).history.length = s.history.length.succ :=
hist_len_apply_move

lemma hist_len_apply_devil_move {s : State} {md : Devil_move} :
  (apply_devil_move s md).history.length = s.history.length.succ :=
hist_len_apply_move

lemma valid_angel_move_ext {pw : ℕ} {b : Board}
  {ma₁ ma₂ : Valid_angel_move pw b}
  (h : ma₁.m = ma₂.m) : ma₁ = ma₂ :=
by { cases ma₁, cases ma₂, congr, exact h }

lemma valid_devil_move_ext {b : Board}
  {md₁ md₂ : Valid_devil_move b}
  (h : md₁.m = md₂.m) : md₁ = md₂ :=
by { cases md₁, cases md₂, congr, exact h }

lemma angel_moves_eq_iff' {pw : ℕ} {s : State}
  {ma₁ ma₂ : Valid_angel_move pw s.board} : ma₁ = ma₂ ↔
  (apply_angel_move s ma₁.m).board = (apply_angel_move s ma₂.m).board :=
begin
  split; intro h, { rw h }, simp_rw [apply_angel_move, apply_move] at h,
  cases h with h₁ h₂, cases ma₁, cases ma₂, simp at h₂ ⊢, exact h₂,
end

lemma devil_moves_eq_iff' {s : State}
  {md₁ md₂ : Valid_devil_move s.board} : md₁ = md₂ ↔
  (apply_devil_move s md₁.m).board = (apply_devil_move s md₂.m).board :=
begin
  split; intro h, { rw h }, simp_rw [apply_devil_move, apply_move] at h,
  cases md₁ with m₁ h₁, cases md₂ with m₂ h₂,
  apply valid_devil_move_ext, dsimp at h ⊢,
  cases m₁ with p₁; cases m₂ with p₂; simp_rw apply_devil_move' at h,
  { cases h₂ with h₂ h₃, contrapose! h₃, rw h, simp },
  { cases h₁ with h₁ h₃, contrapose! h₃, rw ←h, simp },
  { replace h := h.1, replace h₁ := h₁.2, replace h₂ := h₂.2, congr,
    rw set.ext_iff at h, have h₃ := h p₁, simp at h₃, exact h₃ h₁ },
end

lemma angel_moves_eq_iff {pw : ℕ} {s : State}
  {ma₁ ma₂ : Valid_angel_move pw s.board} :
  ma₁ = ma₂ ↔ apply_angel_move s ma₁.m = apply_angel_move s ma₂.m :=
begin
  split; intro h, { rw h }, simp_rw [apply_angel_move, apply_move] at h,
  exact valid_angel_move_ext h.1.2,
end

lemma devil_moves_eq_iff {s : State}
  {md₁ md₂ : Valid_devil_move s.board} :
  md₁ = md₂ ↔ apply_devil_move s md₁.m = apply_devil_move s md₂.m :=
begin
  split; intro h, { rw h }, simp_rw [apply_devil_move, apply_move] at h,
  replace h := h.1, cases md₁ with m₁ h₁, cases md₂ with m₂ h₂,
  apply valid_devil_move_ext, dsimp at h ⊢,
  cases m₁ with p₁; cases m₂ with p₂; simp_rw apply_devil_move' at h,
  { cases h₂ with h₂ h₃, contrapose! h₃, rw h, simp },
  { cases h₁ with h₁ h₃, contrapose! h₃, rw ←h, simp },
  { replace h := h.1, replace h₁ := h₁.2, replace h₂ := h₂.2, congr,
    rw set.ext_iff at h, have h₃ := h p₁, simp at h₃, exact h₃ h₁ },
end

lemma angel_set_move_eq_pos {pw : ℕ} {a : Angel pw} {s : State}
  {ma : Valid_angel_move pw s.board} {hs h} :
  (a.set_move s ma).f s hs h = ma :=
by { rw Angel.set_move, dsimp, split_ifs; refl }

lemma devil_set_move_eq_pos {d : Devil} {s : State}
  {md : Valid_devil_move s.board} {hs} :
  (d.set_move s md).f s hs = md :=
by { rw Devil.set_move, dsimp, split_ifs; refl }

lemma state_eq_of_apply_angel_move_eq {s₁ s₂ : State}
  {ma₁ ma₂ : Angel_move}
  (h : apply_angel_move s₁ ma₁ = apply_angel_move s₂ ma₂) :
  s₁ = s₂ :=
begin
  cases s₁ with b₁ t₁ a₁, cases s₂ with b₂ t₂ a₂,
  simp_rw [apply_angel_move, apply_move] at h, simp only,
  rcases h with ⟨⟨h₁, h₂⟩, h₃, h₄⟩, rw snoc_eq_snoc_iff at h₃, cc,
end

lemma state_eq_of_apply_devil_move_eq {s₁ s₂ : State}
  {ma₁ ma₂ : Devil_move}
  (h : apply_devil_move s₁ ma₁ = apply_devil_move s₂ ma₂) :
  s₁ = s₂ :=
begin
  cases s₁ with b₁ t₁ a₁, cases s₂ with b₂ t₂ a₂,
  cases ma₁ with p₁; cases ma₂ with p₂;
  simp_rw [apply_devil_move, apply_devil_move', apply_move, snoc_eq_snoc_iff] at h;
  simp only; tauto!,
end