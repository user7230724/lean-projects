import tactic.induction
import data.int.basic
import data.set.basic

import .point

structure Board : Type :=
(squares : set Point)
(angel : Point)

def board₀ : Board := ⟨set.univ, center⟩
instance : inhabited Board := ⟨board₀⟩