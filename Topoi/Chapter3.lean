import Topoi.Exponentials
import Topoi.Dual
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square

open CategoryTheory Category Limits

set_option linter.unusedSectionVars false

noncomputable section

variable (𝓒 : Type u) [Category 𝓒]

namespace «CH.3»

namespace «§3.1»
-- Monic arrows

#check Mono

namespace Excercises

variable {a b c : 𝓒} (f : a ⟶ b) (g : b ⟶ c)

lemma «(1)» : Mono f ∧ Mono g → Mono (f ≫ g) := by
  intro ⟨⟨hf⟩, ⟨hg⟩⟩
  constructor
  intro x f₁ f₂ hf₁
  rw [← assoc, ← assoc] at hf₁
  have := hg _ _ hf₁
  apply hf _ _ this

lemma «(2)» : Mono (f ≫ g) → Mono f := by
  intro ⟨hfg⟩
  constructor
  intro x f₁ f₂ hf
  have : f₁ ≫ f ≫ g = f₂ ≫ f ≫ g := by
    rw [← assoc, hf, assoc]
  apply hfg _ _ this

-- NOTE: 教科書にはないが後で使うので追加
lemma «(2)'» : Epi (f ≫ g) → Epi g := by
  intro ⟨hfg⟩
  constructor
  intro x f₁ f₂ hf
  apply hfg
  rw [assoc, hf, assoc]

end Excercises

end «§3.1»

namespace «§3.2»
-- Epic arrows

#check Epi

end «§3.2»

namespace «§3.3»
-- Iso arrows

theorem «lemma 1» {a b : 𝓒} (f : a ⟶ b) : IsIso f → Epi f ∧ Mono f := by
  intro hf
  constructor
  . constructor
    intro c g h hgh
    rw [← id_comp g, ← hf.inv_hom_id, assoc, hgh, ← assoc, hf.inv_hom_id, id_comp]
  constructor
  intro c g h hgh
  calc
    g
    _ = g ≫ 𝟙 a := by rw [comp_id]
    _ = g ≫ (f ≫ inv f) := by rw [hf.hom_inv_id]
    _ = (g ≫ f) ≫ inv f := by rw [assoc]
    _ = (h ≫ f) ≫ inv f := by rw [hgh]
    _ = h ≫ (f ≫ inv f) := by rw [assoc]
    _ = h ≫ 𝟙 a := by rw [hf.hom_inv_id]
    _ = h := by rw [comp_id]

namespace Excercises

lemma «1» {X : 𝓒} : IsIso (𝟙 X) := ⟨by
  use 𝟙 X
  aesop_cat
⟩

lemma «2» {A B : 𝓒} (f : A ⟶ B) (hf : IsIso f) : IsIso (inv f) := ⟨by
  use f
  aesop_cat
⟩

lemma «3» {A B C : 𝓒} (g : A ⟶ B) (f : B ⟶ C) : IsIso f ∧ IsIso g → IsIso (g ≫ f) := by
  intro ⟨⟨finv, finv_id, invf_id⟩, ⟨ginv, ginv_id, invg_id⟩⟩
  constructor
  use finv ≫ ginv
  constructor
  . rw [assoc, ← assoc f, finv_id, id_comp, ginv_id]
  rw [assoc, ← assoc ginv, invg_id, id_comp, invf_id]

end Excercises

end «§3.3»

namespace «§3.4»
-- Isomorphisms objects

#check Skeletal

namespace Excercises

def «1.(i)» {a : 𝓒} : a ≅ a where
  hom := 𝟙 _
  inv := _

def «1.(ii)» {a b : 𝓒} (h : a ≅ b) : b ≅ a where
  hom := h.inv
  inv := h.hom

def «1.(iii)» {a b c : 𝓒} (i₁ : a ≅ b) (i₂ : b ≅ c) : a ≅ c where
  hom := i₁.hom ≫ i₂.hom
  inv := i₂.inv ≫ i₁.inv

end Excercises

end «§3.4»

namespace «§3.5»
-- Initial objects

variable [HasInitial 𝓒]

#check ⊥_ 𝓒
#check IsInitial (⊥_ 𝓒)

end «§3.5»

namespace «§3.6»
-- Terminal objects

variable [HasTerminal 𝓒]

#check ⊤_ 𝓒
#check IsTerminal (⊤_ 𝓒)

lemma terminal_id : terminal.from (⊤_ 𝓒) = 𝟙 (⊤_ 𝓒) := by ext

namespace Excercises

def «1» {a a' : 𝓒} (ha : IsTerminal a) (ha' : IsTerminal a') : a ≅ a' where
  hom := ha'.from a
  inv := ha.from a'

lemma «3» {a : 𝓒} (f : ⊤_ 𝓒 ⟶ a) : Mono f := by
  constructor
  intro x g h hgh
  ext

end Excercises

end «§3.6»

namespace «§3.7»
-- Duality

#check IsDiscrete

lemma «Example 1» : IsDiscrete 𝓒 → 𝓒ᵒᵖ = 𝓒 := by
  intro h
  sorry

lemma «Example 3» : (𝓒ᵒᵖ)ᵒᵖ = 𝓒 := by
  sorry

end «§3.7»

namespace «§3.8»
-- Products

variable [HasBinaryProducts 𝓒]

namespace Excercises

open prod

variable {a b c d e e' : 𝓒}

-- prod.lift_fst_snd
lemma «1» : lift fst snd = 𝟙 (a ⨯ b) := by
  ext
  . rw [lift_fst, id_comp]
  . rw [lift_snd, id_comp]

lemma «2» (f k : c ⟶ a) (g h : c ⟶ b) : lift f g = lift k h → f = k ∧ g = h := by
  intro hf
  constructor
  . rw [← lift_fst f g, ← lift_fst k h, hf]
  . rw [← lift_snd f g, ← lift_snd k h, hf]

-- prod.comp_lift
lemma «3» (f : c ⟶ a) (g : c ⟶ b) (h : d ⟶ c)
    : lift (h ≫ f) (h ≫ g) = h ≫ lift f g := by
  ext
  . rw [lift_fst, assoc, lift_fst]
  rw [lift_snd, assoc, lift_snd]

-- Limits.prod.rightUnitor
def «4» [HasTerminal 𝓒] : a ≅ a ⨯ (⊤_ 𝓒) where
  hom := lift (𝟙 a) (terminal.from a)
  inv := fst
  hom_inv_id := lift_fst (𝟙 a) _
  inv_hom_id := by
    rw [comp_lift, comp_id, terminal.comp_from]
    ext
    . rw [lift_fst, id_comp]


section

variable [HasBinaryCoproducts 𝓒] [HasInitial 𝓒]
-- «4»を双対化した構成
-- 同型の射がなんであるか必要ない場合はこれが使える
open Opposite in
def «4'» : a ≅ a ⨿ (⊥_ 𝓒) := by
  have : op a ≅ op a ⨯ ⊤_ 𝓒ᵒᵖ := «4» (𝓒 := 𝓒ᵒᵖ) (a := op a)
  have h₁ : op a ⨯ ⊤_ 𝓒ᵒᵖ ≅ op a ⨯ op (⊥_ 𝓒) := prod.mapIso (Iso.refl _) Dual.opBotTopOp.symm
  have h₂ : op a ⨯ op (⊥_ 𝓒) ≅ op (a ⨿ ⊥_ 𝓒) := Dual.opCoprodIsoProd a _ |>.symm
  apply this ≪≫ h₁ ≪≫ h₂ |>.unop.symm

-- 5章で具体的な中身が必要だったため作成

def «4''» : a ≅ a ⨿ (⊥_ 𝓒) where
  hom := coprod.inl
  inv := coprod.desc (𝟙 _) (initial.to _)
  hom_inv_id := by rw [coprod.inl_desc]
  inv_hom_id := by
    rw [coprod.desc_comp, initial.to_comp, id_comp]
    ext
    rw [coprod.inl_desc, comp_id]

def «4'''» : a ≅ (⊥_ 𝓒) ⨿ a where
  hom := coprod.inr
  inv := coprod.desc (initial.to _) (𝟙 _)
  hom_inv_id := by rw [coprod.inr_desc]
  inv_hom_id := by
    rw [coprod.desc_comp, initial.to_comp, id_comp]
    ext
    rw [coprod.inr_desc, comp_id]

end

lemma «5» : prod.map (𝟙 a) (𝟙 b) = 𝟙 (a ⨯ b) := by
  ext
  . rw [map_fst, id_comp, comp_id]
  . rw [map_snd, id_comp, comp_id]

-- prod.braiding
def «6» : a ⨯ b ≅ b ⨯ a where
  hom := lift snd fst
  inv := lift snd fst
  hom_inv_id := by
    rw [comp_lift, lift_fst, lift_snd]
    ext
    . rw [lift_fst, id_comp]
    rw [lift_snd, id_comp]
  inv_hom_id := by
    rw [comp_lift, lift_fst, lift_snd]
    ext
    . rw [lift_fst, id_comp]
    rw [lift_snd, id_comp]

-- prod.associator
def «7» : (a ⨯ b) ⨯ c ≅ a ⨯ (b ⨯ c) :=
  let uniq_to_bc : (a ⨯ b) ⨯ c ⟶ b ⨯ c := lift (fst ≫ snd) snd
  let uniq_to_ab : a ⨯ (b ⨯ c) ⟶ a ⨯ b := lift fst (snd ≫ fst)
  { hom := lift (fst ≫ fst) uniq_to_bc
    inv := lift uniq_to_ab (snd ≫ snd)
    hom_inv_id := by
      rw [comp_lift]
      apply Limits.prod.hom_ext
      . rw [lift_fst, id_comp, comp_lift, lift_fst, ← assoc, lift_snd, lift_fst]
        apply Limits.prod.hom_ext
        . rw [lift_fst]
        rw [lift_snd]
      rw [lift_snd, id_comp, ← assoc, lift_snd, lift_snd]
    inv_hom_id := by
      rw [comp_lift]
      ext
      . rw [← assoc, lift_fst, lift_fst, id_comp, lift_fst]
      . rw [lift_snd, comp_lift, lift_fst, ← assoc, lift_fst, lift_snd, id_comp]
      rw [lift_snd, comp_lift, lift_snd, lift_snd, id_comp]
  }

-- prod.lift_map
lemma «8 (i)» (f : a ⟶ b) (g : e ⟶ a) (h : c ⟶ d) (k : e ⟶ c)
    : lift g k ≫ map f h = lift (g ≫ f) (k ≫ h) := by
  ext
  . rw [lift_fst, assoc, map_fst, ← assoc, lift_fst]
  rw [lift_snd, assoc, map_snd, ← assoc, lift_snd]

lemma «8 (ii)» (f : a ⟶ b) (g : e ⟶ a) (h : c ⟶ d) (k : e' ⟶ c)
    : map g k ≫ map f h= map (g ≫ f) (k ≫ h) := by
  ext
  . rw [map_fst, assoc, map_fst, ← assoc, map_fst, assoc]
  rw [map_snd, assoc, map_snd, ← assoc, map_snd, assoc]

end Excercises

end «§3.8»

namespace «§3.9»
-- Coproducts

variable [HasBinaryCoproducts 𝓒]

open coprod

namespace Excercises

variable {a b c d : 𝓒} (f : a ⟶ c) (g : b ⟶ d)

-- Exercise 3
#check map f g

end Excercises

end «§3.9»

namespace «§3.10»
-- Equalizers

open equalizer

variable [HasEqualizers 𝓒]

section
variable {A B : 𝓒} (f : A ⟶ B) (g : A ⟶ B)

-- equalizer.ι_mono
theorem «theorem 1» : Mono (ι f g) := by
  constructor
  intro C j l hjl
  set h := j ≫ ι f g
  have : h ≫ f = h ≫ g :=
    calc
      h ≫ f
      _ = (j ≫ ι f g) ≫ f := rfl
      _ = j ≫ ι f g ≫ f := by rw [assoc]
      _ = j ≫ ι f g ≫ g := by rw [condition]
      _ = (j ≫ ι f g) ≫ g := by rw [← assoc]
      _ = h ≫ g := rfl
  set k := lift h this
  have hk : k ≫ ι f g = h := lift_ι h this

  -- hom_extを使えば初手で証明できちゃう
  have hkj : k = j := hom_ext hk
  have hkl : k = l := hom_ext (hjl ▸ hk)
  apply hkj.symm.trans hkl

theorem «theorem 2» : Epi (ι f g) → IsIso (ι f g) := by
  intro ⟨h⟩
  constructor
  have hfg : f = g := h _ _ (condition _ _)
  set k := lift (𝟙 A) ((id_comp g).symm ▸ (id_comp f).symm ▸ hfg)
  have hki : k ≫ ι f g = 𝟙 _ := lift_ι (𝟙 A) _
  have hik : ι f g ≫ k = 𝟙 _ := by
    have :=
      calc
        (ι f g ≫ k) ≫ ι f g
        _ = ι f g ≫ k ≫ ι f g := by rw [assoc]
        _ = ι f g ≫ 𝟙 _ := by rw [hki]
        _ = ι f g := by rw [comp_id]
        _ = 𝟙 _ ≫ ι f g := by rw [id_comp]
    apply ι_mono.right_cancellation
    apply this
  use k

end

end «§3.10»

namespace «§3.11»
-- Limits and co-limits

#check limit
#check limit.cone
#check limit.π
#check limit.lift

#check colimit

end «§3.11»

namespace «§3.12»
-- coequalizers

end «§3.12»

namespace «§3.13»
-- Pullbacks

open pullback

variable [HasPullbacks 𝓒]

def «Example 6» [HasTerminal 𝓒] {a b d : 𝓒} (f : d ⟶ a) (g : d ⟶ b)
    (hplb : IsPullback f g (terminal.from a) (terminal.from b)) : IsLimit (BinaryFan.mk f g) := by
  let lift_ : (s : BinaryFan a b) → s.pt ⟶ d := λ s ↦ hplb.lift s.fst s.snd <| by simp only [terminal.comp_from]
  apply BinaryFan.isLimitMk lift_
  -- fac
  . intro s
    rw [hplb.lift_fst]
  . intro s
    rw [hplb.lift_snd]
  -- uniq
  intro s m hfst hsnd
  apply hplb.hom_ext
  . rw [hplb.lift_fst, hfst]
  rw [hplb.lift_snd, hsnd]

def «Example 7» {a b e : 𝓒} (i : e ⟶ a) (f g : a ⟶ b) (hplb : IsPullback i i f g)
    : IsLimit (Fork.ofι i hplb.w : Fork f g) := by
  let lift_ : (s : Fork f g) → s.pt ⟶ e := λ s ↦ hplb.lift s.ι s.ι s.condition
  let fi := Fork.ofι i hplb.w
  apply Fork.IsLimit.mk fi lift_
  -- fac
  . intro s
    dsimp [fi]
    rw [hplb.lift_fst s.ι s.ι _]
  -- uniq
  intro s m hm
  apply hplb.hom_ext
  <;> rw [hplb.lift_fst]
  <;> apply hm

namespace «Example 8»

open IsPullback

/-
```
X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
|            |            |
v₁₁          v₁₂          v₁₃
↓            ↓            ↓
X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃
```
-/
variable {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : 𝓒} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
  {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}

lemma «(i)» (s : IsPullback h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) :
    IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) :=
  paste_horiz s t

lemma «(ii)» (hleft : CommSq h₁₁ v₁₁ v₁₂ h₂₁) (s : IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂))
    (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) : IsPullback h₁₁ v₁₁ v₁₂ h₂₁ := of_right s hleft.w t

#check paste_vert
#check of_bot

end «Example 8»

lemma «Example 9» {a b : 𝓒} (f : a ⟶ b)
    : Mono f ↔ IsPullback (𝟙 a) (𝟙 a) f f where
  mp hfm := {
    w := rfl
    isLimit' := ⟨PullbackCone.IsLimit.mk
      rfl
      (PullbackCone.fst ·)
      (λ s ↦ by rw [comp_id])
      (λ s ↦ by rw [comp_id]; apply hfm.right_cancellation; apply s.condition)
      (λ s m hf hs↦ by dsimp; apply (comp_id m) ▸ hf)
    ⟩
  }
  mpr hpb := by
    constructor
    intro _ g h hf
    have fst := hpb.lift_fst g h hf
    have snd := hpb.lift_snd g h hf
    rw [← fst]
    apply snd

lemma «Exercise» {a b c d : 𝓒} (s₁ : a ⟶ c) (s₂ : b ⟶ d)
    (f : c ⟶ d) (g : a ⟶ b) (hpb : IsPullback s₁ g f s₂)
    : Mono f → Mono g := by
  intro ⟨hf⟩
  constructor
  intro _ i j hij
  apply hpb.hom_ext
  . apply hf
    rw [assoc, assoc, hpb.w, ← assoc, hij, assoc]
  apply hij

end «§3.13»

namespace «§3.14»
-- Pushouts

end «§3.14»

namespace «§3.15»
-- Completeness

section

universe w

#check HasLimits
#check HasColimits
-- def Completeness.{u, v} : Prop := ∀ (𝓙 : Type u) [Category.{v, u} 𝓙], HasLimitsOfShape 𝓙 𝓒
-- -- TODO: Mathlib.CategoryTheory.Limits.HasLimitsのHasLimitsが該当した
-- def FiniteCompleteness.{u, v} : Prop := ∀ (𝓙 : Type u) [Category.{v, u} 𝓙] [Finite 𝓙], HasLimitsOfShape 𝓙 𝓒
-- def FiniteCoCompleteness.{u, v} : Prop := ∀ (𝓙 : Type u) [Category.{v, u} 𝓙] [Finite 𝓙], HasColimitsOfShape 𝓙 𝓒

-- 教科書に証明が無い
theorem «Theorem 1» [HasTerminal 𝓒] [HasPullbacks 𝓒] : HasLimits 𝓒 := sorry
theorem «Theorem 1'» [HasInitial 𝓒] [HasPushouts 𝓒] : HasColimits 𝓒 := sorry

end

def «Exercise 1» {a b d : 𝓒} [HasPullbacks 𝓒] [HasBinaryProducts 𝓒] (f g : a ⟶ b) (p q : d ⟶ a)
    (hpb : IsPullback q p (prod.lift (𝟙 a) g) (prod.lift (𝟙 a) f)) (h : p = q)  -- h は3.8章から導かれるらしいが見つからない
    : IsLimit (Fork.ofι p (h ▸ hpb.w) : Fork (prod.lift (𝟙 a) g) (prod.lift (𝟙 a) f)) := by
  let lift_ : (s : Fork _ _) → s.pt ⟶ d := λ s ↦ hpb.lift s.ι s.ι s.condition
  let fi := Fork.ofι p (h.symm ▸ hpb.w)
  apply Fork.IsLimit.mk fi lift_
  . intro s
    dsimp [fi, lift_]
    rw [hpb.lift_snd]
  intro s m hm
  dsimp [fi] at hm
  apply hpb.hom_ext
  . rw [hpb.lift_fst]
    rw [← h, hm]
  rw [hpb.lift_snd]
  rw [hm]

end «§3.15»
namespace «§3.16»
-- Exponentiations

class CartesianClosed where
  finite_complete: HasLimits 𝓒
  has_binary_products: HasBinaryProducts 𝓒 := by apply finite_complete
  has_exponentials: HasExponentials 𝓒

section

variable [CartesianClosed 𝓒]

instance : HasLimits 𝓒 := CartesianClosed.finite_complete
instance : HasExponentials 𝓒 := CartesianClosed.has_exponentials

end

namespace «Theorem 1»

variable [CartesianClosed 𝓒] [HasInitial 𝓒]

variable {𝓒}

def «(1)» {a : 𝓒} : ⊥_ 𝓒 ≅ a ⨯ (⊥_ 𝓒) := by
  have (b : 𝓒) : (a ⨯ (⊥_ 𝓒) ⟶ b) ≃ (⊥_ 𝓒 ⟶ a ⇨' b) := exp.prodEquiv
  have huniq (b : 𝓒) : Unique (a ⨯ (⊥_ 𝓒) ⟶ b) := Equiv.unique (this b)
  have hinit : IsInitial (a ⨯ (⊥_ 𝓒)) := IsInitial.ofUnique _
  apply initialIsoIsInitial hinit

def «(1)'» {a : 𝓒} : ⊥_ 𝓒 ≅ (⊥_ 𝓒) ⨯ a := by
  apply «(1)» ≪≫ prod.braiding _ _

def «(2)» {a : 𝓒} (f : a ⟶ ⊥_ 𝓒) : a ≅ ⊥_ 𝓒 := by
  suffices h : a ≅ a ⨯ ⊥_ 𝓒 from by
    apply h ≪≫ «(1)».symm
  have : a ≅ a ⨯ ⊥_ 𝓒 := {
    hom := prod.lift (𝟙 a) f
    inv := prod.fst
    hom_inv_id := by
      rw [prod.lift_fst]
    inv_hom_id := by
      apply IsInitial.hom_ext
      apply IsInitial.ofIso initialIsInitial
      apply «(1)»
  }
  apply this

def «(3)» (h : ⊥_ 𝓒 ≅ ⊤_ 𝓒) : ∀ a b : 𝓒, a ≅ b := by
  intro a b
  let fa := terminal.from a ≫ h.inv
  let fb := terminal.from b ≫ h.inv
  have ha : a ≅ ⊥_ 𝓒 := «(2)» fa
  have hb : b ≅ ⊥_ 𝓒 := «(2)» fb
  apply ha ≪≫ hb.symm

def «(4)» {a : 𝓒} (f : ⊥_ 𝓒 ⟶ a) : Mono f := by
  constructor
  intro b g h hf
  have hb : b ≅ ⊥_ 𝓒 := «(2)» g
  calc
    g
    _ = (𝟙 _) ≫ g := by rw [id_comp]
    _ = (hb.hom ≫ hb.inv) ≫ g := by rw [hb.hom_inv_id]
    _ = hb.hom ≫ hb.inv ≫ g := by rw [assoc]
    _ = hb.hom ≫ hb.inv ≫ h := by rw [initial.hom_ext (hb.inv ≫ g) (hb.inv ≫ h)]
    _ = (hb.hom ≫ hb.inv) ≫ h := by rw [assoc]
    _ = (𝟙 _) ≫ h :=  by rw [hb.hom_inv_id]
    _ = h := by rw [id_comp]

-- NOTE: もっとシンプルな証明がある気がする
def «(5).1» {a : 𝓒} : (⊤_ 𝓒) ⇨' a ≅ a := by
  have : (⊤_ 𝓒) ⨯ (⊤_ 𝓒) ⇨' a ≅ (⊤_ 𝓒) ⨯ a := {
    hom := exp.eval ≫ prod.lift (terminal.from a) (𝟙 _)
    inv := prod.map (𝟙 _) (exp.curry prod.snd)
    hom_inv_id := by
      rw [assoc, prod.lift_map, id_comp, comp_id, prod.comp_lift, terminal.comp_from]
      apply Limits.prod.hom_ext
      . rw [prod.lift_fst, id_comp]
        apply terminal.hom_ext
      rw [prod.lift_snd, id_comp]
      rw [exp.comp_curry, prod.map_snd]
      symm
      apply exp.uniq'
      rw [exp.uncurry]
      have {b : 𝓒}: prod.map (𝟙 (⊤_ 𝓒)) (prod.snd : (⊤_ 𝓒) ⨯ b ⟶ b) = prod.snd := by
        ext
        rw [prod.map_snd]
      rw [this]
    inv_hom_id := by
      rw [← assoc, ← exp.uncurry, exp.fac', prod.comp_lift, terminal.comp_from, comp_id]
      aesop_cat
  }
  apply (prod.leftUnitor ((⊤_ 𝓒) ⇨' a)).symm ≪≫ this ≪≫ (prod.leftUnitor a)

def «(5).2» {a : 𝓒} : (⊥_ 𝓒) ⇨' a ≅ ⊤_ 𝓒 := by
  have (b : 𝓒) : Unique (b ⟶ (⊥_ 𝓒) ⇨' a) := by
    have h: Unique ((⊥_ 𝓒) ⨯ b ⟶ a) := Iso.homFromEquiv «(1)'» |>.symm |>.unique
    apply Equiv.unique exp.prodEquiv.symm
  have : IsTerminal ((⊥_ 𝓒) ⇨' a) := IsTerminal.ofUnique _
  apply terminalIsoIsTerminal this |>.symm

def «(5).3» {a : 𝓒} : a ⇨' ⊤_ 𝓒 ≅ ⊤_ 𝓒 := by
  have (b : 𝓒) : Unique (b ⟶ a ⇨' ⊤_ 𝓒) := exp.prodEquiv.symm.unique
  have : IsTerminal (a ⇨' ⊤_ 𝓒) := IsTerminal.ofUnique _
  apply terminalIsoIsTerminal this |>.symm

-- iniitialではなくIsInitial用の各定理
namespace IsInitial

variable {a I : 𝓒} (hI : IsInitial I)

def «(1)» : I ≅ a ⨯ I := by
  apply initialIsoIsInitial hI |>.symm.trans
  apply «CH.3».«§3.16».«Theorem 1».«(1)» (a := a) |>.trans
  apply prod.mapIso (.refl _) (initialIsoIsInitial hI)

def «(2)» {a I : 𝓒} (hI : IsInitial I) (f : a ⟶ I) : a ≅ I := by
  suffices h : a ≅ a ⨯ I from by
    apply h ≪≫ («(1)» hI).symm
  apply show a ≅ a ⨯ I from {
    hom := prod.lift (𝟙 a) f
    inv := prod.fst
    hom_inv_id := by
      rw [prod.lift_fst]
    inv_hom_id := by
      apply IsInitial.hom_ext
      apply IsInitial.ofIso initialIsInitial
      apply initialIsoIsInitial hI |>.trans
      apply «(1)» hI
  }

def «(4)»  (f : I ⟶ a) : Mono f := by
  constructor
  intro b g h hf
  have hb : b ≅ I := «(2)» hI g
  calc
    g
    _ = (𝟙 _) ≫ g := by rw [id_comp]
    _ = (hb.hom ≫ hb.inv) ≫ g := by rw [hb.hom_inv_id]
    _ = hb.hom ≫ hb.inv ≫ g := by rw [assoc]
    _ = hb.hom ≫ hb.inv ≫ h := by rw [hI.hom_ext (hb.inv ≫ g) (hb.inv ≫ h)]
    _ = (hb.hom ≫ hb.inv) ≫ h := by rw [assoc]
    _ = (𝟙 _) ≫ h :=  by rw [hb.hom_inv_id]
    _ = h := by rw [id_comp]

end IsInitial

end «Theorem 1»

end «§3.16»

end «CH.3»
