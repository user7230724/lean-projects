import tactic
import tactic.induction

noncomputable theory
open_locale classical

namespace test

notation f ` # `:1 a:0 := f a

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

axiom true_ne_false : true ≠ false
axiom prop_ind (F : Prop → Prop) {P : Prop} (h₁ : F true) (h₂ : F false) : F P

-----

lemma id {P : Prop} (h : P) : P :=
h

lemma trivial : true :=
λ _, id

lemma not_false : not false :=
id

lemma not_not_intro {P : Prop} (h : P) : ¬¬P :=
λ h₁, h₁ h

lemma not_not_elim {P : Prop} (h : ¬¬P) : P :=
prop_ind (λ P, ¬¬P → P) (λ _, trivial) (λ h₁, h₁ not_false) h

lemma lem {P : Prop} : P ∨ ¬P := id

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

-----

end test