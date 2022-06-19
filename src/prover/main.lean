import tactic
import tactic.induction

noncomputable theory
open_locale classical

namespace test

notation f ` # `:1 a:0 := f a

def id {α : Sort*} (x : α) : α := x

-----

def true : Prop :=
∀ (P : Prop), P → P

def false : Prop :=
∀ (P : Prop), P

def not (P : Prop) : Prop :=
P → false

local prefix `¬`:40 := not

def or (P Q : Prop) : Prop :=
¬P → Q

local infixr ` ∨ `:30 := or

def and (P Q : Prop) : Prop :=
¬(¬P ∨ ¬Q)

local infixr ` ∧ `:35 := and

def iff (P Q : Prop) : Prop :=
(P → Q) ∧ (Q → P)

local infixl ` ↔ `:20 := iff

def eq {α : Type} (x y : α) : Prop :=
∀ (P : α → Prop), P x → P y

local infixl ` = `:50 := eq

def ne {α : Type} (x y : α) : Prop :=
¬(x = y)

local infixl ` ≠ `:50 := ne

-----

axiom prop_rec (F : Prop → Prop) {P : Prop} (h₁ : F true) (h₂ : F false) : F P

-----

lemma trivial : true :=
λ _, id

lemma not_false : not false :=
id

lemma not_not_intro {P : Prop} (h : P) : ¬¬P :=
λ h₁, h₁ h

lemma not_not_elim {P : Prop} (h : ¬¬P) : P :=
prop_rec (λ x, ¬¬x → x) (λ _, trivial) (λ h₁, h₁ not_false) h

lemma em {P : Prop} : P ∨ ¬P := id

lemma false_elim {P : Prop} (h : false) : P :=
h P

lemma or_intro₁ {P Q : Prop} (h : P) : P ∨ Q :=
λ h₁, false_elim (h₁ h)

lemma or_intro₂ {P Q : Prop} (h : Q) : P ∨ Q :=
λ _, h

lemma mt {P Q : Prop} (h₁ : P → Q) (h₂ : ¬Q) : ¬P :=
λ h₃, h₂ # h₁ h₃

lemma or_elim {P Q R : Prop} (h₁ : P ∨ Q) (h₂ : P → R) (h₃ : Q → R) : R :=
not_not_elim # λ h₄, h₄ # h₃ # h₁ # mt h₂ h₄

lemma and_intro {P Q : Prop} (h₁ : P) (h₂ : Q) : P ∧ Q :=
λ h₃, or_elim h₃ (λ h₄, h₄ h₁) (λ h₄, h₄ h₂)

lemma and_elim₁ {P Q : Prop} (h : P ∧ Q) : P :=
not_not_elim # λ h₁, h # or_intro₁ h₁

lemma and_elim₂ {P Q : Prop} (h : P ∧ Q) : Q :=
not_not_elim # λ h₁, h # or_intro₂ h₁

lemma iff_intro {P Q : Prop} (h₁ : P → Q) (h₂ : Q → P) : P ↔ Q :=
and_intro h₁ h₂

lemma iff_elim₁ {P Q : Prop} (h : P ↔ Q) : P → Q :=
and_elim₁ h

lemma iff_elim₂ {P Q : Prop} (h : P ↔ Q) : Q → P :=
and_elim₂ h

lemma mp {P Q : Prop} (h : P ↔ Q) : P → Q :=
iff_elim₁ h

lemma mpr {P Q : Prop} (h : P ↔ Q) : Q → P :=
iff_elim₂ h

lemma true_ne_false : true ≠ false :=
λ h, h id trivial

lemma not_not {P : Prop} : ¬¬P ↔ P :=
iff_intro not_not_elim not_not_intro

lemma iff_rec (F : Prop → Prop) {P Q : Prop} (h₁ : P ↔ Q) (h₂ : F P) : F Q :=
prop_rec (λ x, (x ↔ Q) → F x → F Q)
(@prop_rec (λ x, (true ↔ x) → F true → F x) Q (λ _, id) (λ h₃, false_elim # mp h₃ trivial))
(@prop_rec (λ x, (false ↔ x) → F false → F x) Q (λ h₃, false_elim # mpr h₃ trivial) (λ _, id))
h₁ h₂

lemma eq_refl {α : Type} {x : α} : x = x :=
λ _, id

lemma rfl {α : Type} {x : α} : x = x :=
eq_refl

lemma eq_comm {α : Type} {x y : α} (h : x = y) : y = x :=
not_not_elim # λ h₁, mt (h (λ z, z = x)) h₁ rfl

lemma eq_iff {α : Type} {x y : α} : x = y ↔ (∀ (P : α → Prop), P x ↔ P y) :=
iff_intro (λ h P, iff_intro (h P) (eq_comm h P)) (λ h, mp (h (λ z, x = z)) rfl)

-----

end test