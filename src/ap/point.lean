import tactic.induction
import data.int.basic
import data.set.basic

import .base

noncomputable theory
open_locale classical

instance : inhabited Point := ⟨center⟩