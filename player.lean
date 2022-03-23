import tactic.induction
import data.int.basic
import data.set.basic

import .point .dist .board .state

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

def apply_move (s : State) (b : Board) : State :=
{ board := b, history := s.board :: s.history }

def apply_angel_move (s : State) (p : Angel_move) : State :=
apply_move s {s.board with angel := p}

def apply_devil_move' (s : State) : Devil_move → Board
| (option.none) := s.board
| (option.some p) := {s.board with squares := s.board.squares \ {p}}

def apply_devil_move (s : State) (m : Devil_move) : State :=
apply_move s (apply_devil_move' s m)

-----

structure Angel (pw : ℕ) : Type :=
(f : Π (s : State),
  angel_has_valid_move pw s.board → Valid_angel_move pw s.board)

structure Devil : Type :=
(f : Π (s : State), Valid_devil_move s.board)

instance {pw : ℕ} : inhabited (Angel pw) :=
⟨⟨λ s h, ⟨h.some, h.some_spec⟩⟩⟩

instance : inhabited Devil :=
⟨⟨λ s, ⟨none, trivial⟩⟩⟩

def Angel.sup {pw pw₁ : ℕ} (a₁ : Angel pw₁) (a : Angel pw) : Prop :=
∀ s h, ∃ h₁, (a₁.f s h₁).m = (a.f s h).m

def Angel.sub {pw₁ pw : ℕ} (a : Angel pw₁) (a₁ : Angel pw) : Prop :=
a₁.sup a

def Angel_prev_moves (pw : ℕ) (s : State) :=
Π (s₁ : State), s₁.history.length < s.history.length →
angel_has_valid_move pw s₁.board → Valid_angel_move pw s₁.board

def Devil_prev_moves (s : State) :=
Π (s₁ : State), s₁.history.length < s.history.length →
Valid_devil_move s₁.board

def Angel.set_prev_moves {pw : ℕ} (a : Angel pw) (s : State)
  (pm : Angel_prev_moves pw s) : Angel pw :=
begin
  refine ⟨λ s₁ h₁, _⟩,
  apply dite (s₁.history.length < s.history.length); intro h₂,
  { exact pm s₁ h₂ h₁ },
  { exact a.f s₁ h₁ },
end

def Devil.set_prev_moves (d : Devil) (s : State)
  (pm : Devil_prev_moves s) : Devil :=
begin
  refine ⟨λ s₁, _⟩,
  apply dite (s₁.history.length < s.history.length); intro h₁,
  { exact pm s₁ h₁ },
  { exact d.f s₁ },
end

def Angel.set_move {pw : ℕ} (a : Angel pw) (s : State)
  (ma : Valid_angel_move pw s.board) : Angel pw :=
begin
  refine ⟨λ s₁ h, _⟩, apply dite (s₁ = s); intro h₁,
  { cases h₁, exact ma },
  { exact a.f s₁ h },
end

def Devil.set_move (d : Devil) (s : State)
  (md : Valid_devil_move s.board) : Devil :=
begin
  refine ⟨λ s₁, _⟩, apply dite (s₁ = s); intro h₁,
  { cases h₁, exact md },
  { exact d.f s₁ },
end

def Angel.prev_moves_id {pw : ℕ} (a : Angel pw) (s : State) : Angel pw :=
a.set_prev_moves s (λ s₁ _ h, a.f s₁ h)

def Devil.prev_moves_id (d : Devil) (s : State) : Devil :=
d.set_prev_moves s (λ s₁ h, d.f s₁)

def Angel.prev_moves_set {pw : ℕ} (a : Angel pw) (s : State)
  (s₁ : State) (m : Valid_angel_move pw s₁.board)
  (h : s₁.history.length < s.history.length) : Angel pw :=
begin
  apply a.set_prev_moves s, rintro s₂ h₁ h₂,
  apply dite (s₂ = s₁); intro h₃,
  { cases h₃, exact m },
  { exact a.f s₂ h₂ },
end

def Devil.prev_moves_set (d : Devil) (s : State)
  (s₁ : State) (m : Valid_devil_move s₁.board)
  (h : s₁.history.length < s.history.length) : Devil :=
begin
  apply d.set_prev_moves s, rintro s₂ h₁,
  apply dite (s₂ = s₁); intro h₂,
  { cases h₂, exact m },
  { exact d.f s₂ },
end

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
  a₁ = a₂ ↔ ∀ s h, a₁.f s h = a₂.f s h :=
begin
  split; intro h,
  { subst h, simp },
  { cases a₁ with f₁, cases a₂ with f₂, congr, ext, apply h },
end

lemma devils_eq_iff {d₁ d₂ : Devil} :
  d₁ = d₂ ↔ ∀ s, d₁.f s = d₂.f s :=
begin
  split; intro h,
  { subst h, simp },
  { cases d₁ with f₁, cases d₂ with f₂, congr, ext, apply h },
end

lemma angel_prev_moves_id_eq {pw : ℕ} {a : Angel pw} {s : State} :
  a.prev_moves_id s = a :=
by { rw angels_eq_iff, rintro s₁ h, change dite _ _ _ = _, split_ifs; refl }

lemma devil_prev_moves_id_eq {d : Devil} {s : State} :
  d.prev_moves_id s = d :=
by { rw devils_eq_iff, rintro s₁, change dite _ _ _ = _, split_ifs; refl }

lemma angel_set_move_eq {pw : ℕ} {a : Angel pw}
  {s : State} {m : Valid_angel_move pw s.board} {h} :
  (a.set_move s m).f s h = m :=
by { change dite _ _ _ = _, split_ifs with h₁; refl }

lemma devil_set_move_eq {d : Devil}
  {s : State} {m : Valid_devil_move s.board} :
  (d.set_move s m).f s = m :=
by { change dite _ _ _ = _, split_ifs with h₁; refl }

lemma angel_set_move_self {pw : ℕ} {a : Angel pw}
  {s : State} {h} : a.set_move s (a.f s h) = a :=
begin
  rw angels_eq_iff; intros, change dite _ _ _ = _, split_ifs with h₂,
  { subst h₂ }, { refl },
end

lemma devil_set_move_self {d : Devil}
  {s : State} : d.set_move s (d.f s) = d :=
begin
  rw devils_eq_iff; intros, change dite _ _ _ = _, split_ifs with h₂,
  { subst h₂ }, { refl },
end

lemma angel_set_move_set_move_eq {pw : ℕ} {a : Angel pw} {s : State}
  {m₁ m₂ : Valid_angel_move pw s.board} :
  (a.set_move s m₁).set_move s m₂ = a.set_move s m₂ :=
begin
  rw angels_eq_iff, rintro s₁ h₁,
  change dite _ _ _ = _, split_ifs with h₂,
  { subst h₂, rw angel_set_move_eq },
  { change dite _ _ _ = dite _ _ _, simp_rw dif_neg h₂ },
end

lemma devil_set_move_set_move_eq {d : Devil} {s : State}
  {m₁ m₂ : Valid_devil_move s.board} :
  (d.set_move s m₁).set_move s m₂ = d.set_move s m₂ :=
begin
  rw devils_eq_iff, rintro s₁,
  change dite _ _ _ = _, split_ifs with h₂,
  { subst h₂, rw devil_set_move_eq },
  { change dite _ _ _ = dite _ _ _, simp_rw dif_neg h₂ },
end

lemma angel_prev_moves_set_eq {pw : ℕ} {a : Angel pw} {s s₁ : State}
  {m : Valid_angel_move pw s₁.board} {h} :
  a.prev_moves_set s s₁ m h = a.set_move s₁ m :=
begin
  rw angels_eq_iff, rintro s₂ h,
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
  rw devils_eq_iff, rintro s₂,
  change dite _ _ _ = _, split_ifs with h₁,
  { dsimp, split_ifs with h₂,
    { subst h₂, simp [devil_set_move_eq] },
    { change _ = dite _ _ _, rw dif_neg h₂ }},
  { change _ = dite _ _ _, split_ifs with h₂,
    { subst h₂, contradiction },
    { refl }},
end