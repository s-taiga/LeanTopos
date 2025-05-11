import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

noncomputable section

namespace Dual

open CategoryTheory Opposite Limits

variable {𝓒 : Type*} [Category 𝓒]

section

variable [HasTerminal 𝓒] [HasInitial 𝓒]

def opBotTopOp : op (⊥_ 𝓒) ≅ (⊤_ 𝓒ᵒᵖ) where
  hom := terminal.from <| op (⊥_ 𝓒)
  inv := (initial.to <| unop (⊤_ 𝓒ᵒᵖ)).op
  hom_inv_id := by
    apply Subsingleton.elim
  inv_hom_id := by
    rw [terminal.comp_from]
    ext

end

section

variable [HasBinaryProducts 𝓒] [HasBinaryCoproducts 𝓒]

def opCoprodIsoProd (A B : 𝓒) : op (A ⨿ B) ≅ op A ⨯ op B where
  hom := prod.lift coprod.inl.op coprod.inr.op
  inv := (coprod.desc prod.fst.unop prod.snd.unop).op
  hom_inv_id := by
    sorry
  inv_hom_id := by
    sorry
