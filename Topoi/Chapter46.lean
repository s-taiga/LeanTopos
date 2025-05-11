import Mathlib.CategoryTheory.Action.Limits

open CategoryTheory Limits

noncomputable section

namespace «CH.4»

namespace «§4.6»
-- Monoid actions

variable
  {M : Type u} [Monoid M]
  {V : Type (u + 1)} [LargeCategory V] [HasFiniteLimits V]
  (X Y : Action V M) (f : X ⟶ Y)

#check X.ρ 1

example : X.ρ 1 = 𝟙 _ := by
  apply Action.ρ_one

example {m p : M} : X.ρ p ≫ X.ρ m = X.ρ (m * p) := by
  simp_all only [map_mul, End.mul_def]

example {m : M} : X.ρ m ≫ f.hom = f.hom ≫ Y.ρ m := by
  apply Action.Hom.comm

def terminalObj : Action V M where
  V := ⊤_ V
  ρ := {
    toFun := λ m ↦ terminal.from _
    map_one' := by
      rw [End.one_def]
      apply terminal.hom_ext
    map_mul' := by
      intro x y
      dsimp
      rw [terminal.comp_from]
  }

def terminalObj.hom : X ⟶ terminalObj where
  hom := terminal.from _
  comm := by
    intro g
    dsimp [terminalObj]
    simp only [terminal.comp_from]

example : HasTerminal (Action V M) := by
  apply IsTerminal.hasTerminal (X := terminalObj)
  apply IsTerminal.ofUniqueHom terminalObj.hom
  intro X f
  ext
  dsimp [terminalObj.hom]
  apply terminal.hom_ext

def prodObj : Action V M where
  V := X.V ⨯ Y.V
  ρ := {
    toFun := λ m ↦ prod.map (X.ρ m) (Y.ρ m)
    map_one' := by
      rw [End.one_def]
      simp only [Action.ρ_one]
      apply prod.map_id_id
    map_mul' := by
      intro x y
      dsimp
      simp only [map_mul, End.mul_def]
      rw [prod.map_map]
  }

-- TODO: イデアルの定義方法がわからない
