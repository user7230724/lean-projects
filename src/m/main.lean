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

@[simp] lemma M_const {a : ℕ} : M (λ _, a) = 0 :=
begin
  dsimp, by_cases h : a = 0,
  { simp [h] },
  { rw [eq_true_intro h, nat.Inf_def ⟨0, _⟩], swap, { trivial },
    generalize_proofs h₁, have h₂ : nat.find h₁ ≤ 0 := nat.find_le trivial,
    rw nat.le_zero_iff at h₂, convert h₂ },
end

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