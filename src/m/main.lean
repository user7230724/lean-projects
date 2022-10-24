import tactic
import tactic.induction
import data.nat.lattice

noncomputable theory
open_locale classical

@[simp] def L (a b : ℕ) : ℕ :=
if a ≤ b then 1 else 0

@[simp] def M (f : ℕ → ℕ) : ℕ :=
Inf {n | f n ≠ 0}

---

@[simp] lemma M_const {a : ℕ} : M (λ (b : ℕ), a) = 0 :=
begin
  dsimp, by_cases h : a = 0,
  { simp [h] },
  { rw [eq_true_intro h, nat.Inf_def ⟨0, _⟩], swap, { trivial },
    generalize_proofs h₁, have h₂ : nat.find h₁ ≤ 0 := nat.find_le trivial,
    rw le_zero_iff at h₂, convert h₂ },
end

@[simp] lemma M_id : M (λ (a : ℕ), a) = 1 :=
by { dsimp, rw [nat.Inf_def ⟨1, _⟩]; simp [nat.find_eq_iff] }

@[simp] lemma Inf_ge {a : ℕ} : Inf {b | a ≤ b} = a :=
by { rw nat.Inf_def ⟨a, _⟩; simp [nat.find_eq_iff, le_refl a] }

-- #exit

---

def zero' : ℕ := M (λ (a : ℕ), L a a)

def one' : ℕ := M (λ (a : ℕ), a)

def not' (a : ℕ) : ℕ :=
M (λ (b : ℕ), L (L a zero') b)

def imp' (a b : ℕ) : ℕ :=
M (λ (c : ℕ), L (L a b) c)

def or' (a b : ℕ) : ℕ :=
M (λ (c : ℕ), L (imp' (not' a) b) c)

-- #exit

---

@[simp] lemma zero'_def : zero' = 0 :=
by simp [zero']

@[simp] lemma one'_def : one' = 1 :=
by simp [one']

@[simp] lemma not'_def {a : ℕ} : not' a = if a = 0 then 1 else 0 :=
by simp [not']

@[simp] lemma zero'_imp' {a : ℕ} : imp' zero' a = 1 :=
by simp [imp']

@[simp] lemma imp'_zero' {a : ℕ} : imp' a zero' = not' a :=
by simp [imp']

@[simp] lemma one_imp' {a : ℕ} : imp' 1 a = if a = 0 then 0 else 1 :=
begin
  simp only [imp', M, L, ne.def, ite_eq_right_iff, nat.one_ne_zero,
  not_forall, not_false_iff, exists_prop, and_true, Inf_ge], rw ←ite_not, simp,
end

@[simp] lemma zero'_or' {a : ℕ} : or' zero' a = if a = 0 then 0 else 1 :=
by simp [or']

-- #exit

---

@[simp] def f₁ : ℕ → ℕ :=
λ (a : ℕ), L (L 0 0) (L (M (λ (b : ℕ), 0)) 0)

example {n : ℕ} : f₁ n = 1 :=
by simp

@[simp] def f₂ : ℕ → ℕ :=
λ (a : ℕ), a

example {n : ℕ} : f₂ n = n :=
by simp

@[simp] def f₃ : ℕ → ℕ :=
λ (a : ℕ), (λ (b : ℕ), L 0 ((λ (c : ℕ → ℕ), 0) (λ (c : ℕ), 0)))
  ((λ (b : ℕ → ℕ), 0) (λ (b : ℕ), b))

example {n : ℕ} : f₃ n = 1 :=
by simp

@[simp] def f₄ : ℕ → ℕ :=
λ (a : ℕ), M (λ (b : ℕ), (λ (c : ℕ → ℕ), c ((λ (d : ℕ), L 0 (M (λ (e : ℕ), 0))) a))
  (λ (c : ℕ), L (M (λ (d : ℕ), 0)) 0))

example {n : ℕ} : f₄ n = 0 :=
by simp

@[simp] def f₅ : ℕ → ℕ :=
λ (a : ℕ), L a (L (M (λ (b : ℕ), a)) a)

example {n : ℕ} : f₅ n = if n ≤ 1 then 1 else 0 :=
by simp

@[simp] def f₆ : ℕ → ℕ :=
λ (a : ℕ), L ((λ (b : ℕ), L (M (λ (c : ℕ), b)) a) (M (λ (b : ℕ), b))) a

example {n : ℕ} : f₆ n = if n = 0 then 0 else 1 :=
by { simp only [f₆, L, M_const, zero_le, if_true], rw ←ite_not, simp }