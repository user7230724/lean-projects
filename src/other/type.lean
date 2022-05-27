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
axiom elim : ∀ (P : Nat), Pf 0 → Pf P
axiom psub : ∀ (P : Nat → Nat) (n : Nat), Pf n → Pf (P 1) → Pf (P n)
axiom ind : ∀ (P : Nat → Nat), Pf (P 0) → (∀ (n : Nat), Pf (P n) → Pf (P (succ n))) →
  ∀ (n : Nat), Pf (P n)

-----

def id' {t : Type} (a : t) : t := a
def const {t s : Type} (a : t) (b : s) : t := a

def cases {t : Type} (z : t) (f : Nat → t) (n : Nat) : t :=
rec z (λ k _, f k) n

def pred (n : Nat) : Nat :=
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

lemma elim' : ∀ (P : Nat) (n : Nat), Pf (succ (succ n)) → Pf P :=
λ P n h, elim P (psub (λ n, not' (pred n)) (succ (succ n)) h triv)

lemma cs : ∀ (P : Nat → Nat), Pf (P 0) → (∀ (n : Nat), Pf (P (succ n))) →
  ∀ (n : Nat), Pf (P n) :=
λ P h1 h2, ind P h1 (λ n h3, h2 n)