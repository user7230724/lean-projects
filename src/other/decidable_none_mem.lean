import tactic
import tactic.induction

variable {α : Type}

@[instance]
def d : Π {l : list (option α)}, decidable (none ∈ l)
| [] := decidable.is_false (by simp)
| (none :: _) := decidable.is_true (by simp)
| (some _ :: l) := decidable.rec_on (d : decidable (none ∈ l))
  (λ h, decidable.is_false (by simpa))
  (λ h, decidable.is_true (by simpa))

def g (l : list (option α)) : option (list α) :=
if none ∈ l then none else some l.reduce_option