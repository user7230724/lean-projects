import tactic.induction
import data.int.basic
import data.set.basic

import .base .point

noncomputable theory
open_locale classical

instance : inhabited Board := ⟨board₀⟩