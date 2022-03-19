import tactic.induction
import data.int.basic
import data.set.basic

import .state .move

noncomputable theory
open_locale classical

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