import tactic
import tactic.induction

noncomputable theory
open_locale classical

inductive Nat : Type
| zero : Nat
| succ : Nat → Nat

def succ : Nat → Nat := Nat.succ

instance : has_zero Nat := ⟨Nat.zero⟩
instance : has_one Nat := ⟨succ 0⟩

def rec {t : Type} (z : t) (f : Nat → t → t) : Nat → t
| 0 := z
| (Nat.succ n) := f n (rec n)

-----

constant Pf : Nat → Prop

axiom triv : Pf 1
axiom elim : ∀ (P : Prop), Pf 0 → P
axiom psub : ∀ (P : Nat → Prop) (n : Nat), Pf n → P 1 → P n
axiom ind : ∀ (P : Nat → Prop), P 0 → (∀ (n : Nat), P n → P (succ n)) →
  ∀ (n : Nat), P n

-----

def id' {t : Type} (a : t) : t := a
def const {t s : Type} (a : t) (b : s) : t := a

def cases {t : Type} (z : t) (f : Nat → t) (n : Nat) : t :=
rec z (λ k _, f k) n

def pred' (n : Nat) : Nat :=
cases 0 id n

def Prop' (p : Nat) : Nat :=
cases 1 (cases 1 (const 0)) p

def true' : Nat := 1
def false' : Nat := 0

def ite' {t : Type} (p : Nat) (a b : t) : t :=
cases b (const a) p

def not' (p : Nat) : Nat :=
ite' p false' true'

def and' (p q : Nat) : Nat :=
ite' p q false'

def or' (p q : Nat) : Nat :=
ite' p true' q

def imp (p q : Nat) : Nat :=
ite' p q true'

def iff' (p q : Nat) : Nat :=
ite' p q (not' q)

-----

lemma elim' : ∀ (P : Prop) (n : Nat), Pf (succ (succ n)) → P :=
λ P n h, elim P (id psub (λ x, Pf (not' (pred' x))) _ h triv)

lemma cs : ∀ (P : Nat → Prop), P 0 → (∀ (n : Nat), P (succ n)) →
  ∀ (n : Nat), P n :=
λ P h₁ h₂, ind P h₁ (λ n h₃, h₂ n)

example : ∀ (p q : Nat), Pf p → Pf q → Pf (imp p q) :=
λ p q h₁ h₂, id psub (λ x, Pf (imp x q)) _ h₁ h₂