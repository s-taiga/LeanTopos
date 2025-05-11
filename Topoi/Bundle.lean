import Mathlib.Data.Set.Defs

variable {X : Type u₁} {I : Type u₂} {𝓐 : I → Set X}

def dis : Prop := ∀ i j : I, i ≠ j → 𝓐 i ∩ 𝓐 j = ∅

variable (dis𝓐 : dis)

def A := {x // ∃ i, x ∈ 𝓐 i}

noncomputable def p : (@A X I 𝓐) → I := λ ⟨_, h⟩ ↦ h.choose

-- def stalk (i : I) : Set X := {x | p x = i}
