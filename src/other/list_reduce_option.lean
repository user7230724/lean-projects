import tactic
import tactic.induction
import data.option.basic
import data.list.basic

noncomputable theory
open_locale classical

variables {α : Type} {l : list (option α)}

def f' : option (list α) → list (option α) → option (list α)
| none _ := none
| (some acc) [] := some acc.reverse
| (some acc) (none :: l) := none
| (some acc) (some x :: l) := f' (some (x :: acc)) l

def f : list (option α) → option (list α) :=
f' (some [])

def g (l : list (option α)) : option (list α) :=
if none ∈ l then none else some l.reduce_option

lemma list.reduce_option_reverse :
  l.reverse.reduce_option = l.reduce_option.reverse :=
begin
  induction l using list.reverse_rec_on with l x ih,
  { refl },
  { rw [list.reverse_append, list.reverse_singleton, list.singleton_append,
      list.reduce_option_append, list.reduce_option_singleton], cases x,
    { simpa },
    { rw [list.reduce_option_cons_of_some, list.reverse_append, ih], refl }},
end

lemma list.reduce_option_map_some {l : list α} : (l.map some).reduce_option = l :=
begin
  induction l with x l ih,
  { refl },
  { simpa },
end

lemma aux {l' : list α} : f' (some l') l = g (l'.reverse.map some ++ l) :=
begin
  symmetry,
  induction l with x l ih generalizing l',
  { simp [f', g, list.reduce_option_reverse, list.reduce_option_reverse,
    list.reduce_option_map_some] },
  { cases x; rw f',
    { simp [g] },
    { simp [←ih] }},
end

lemma lem₁ : f l = g l :=
by simp [f, aux]

lemma lem₂ : f l = sequence l :=
begin
  rw [eq_comm, lem₁, g, sequence],
  induction l with x l ih,
  { refl },
  { rw list.traverse_cons, dsimp, cases x,
    { refl },
    { simp only [option.map_some', false_or, list.reduce_option_cons_of_some, ih],
      split_ifs; refl }},
end