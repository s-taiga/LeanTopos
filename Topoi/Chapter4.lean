import Topoi.Chapter3
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.Types.Shapes
import Mathlib.CategoryTheory.Products.Basic

open CategoryTheory Category Limits

set_option linter.unusedSectionVars false

noncomputable section

variable {𝓒 : Type*} [Category 𝓒]

namespace «CH.4»

namespace «§4.1»
-- Subobjects

def subset (d : 𝓒) := Σ' (a : 𝓒) (f : a ⟶ d), Mono f

variable {d : 𝓒}

namespace subset

variable (f : subset d)
abbrev dom : 𝓒 := f.1
abbrev ar : f.dom ⟶ d := f.2.1
abbrev mono : Mono f.ar := f.2.2

abbrev mk {a : 𝓒} (f : a ⟶ d) [Mono f] : subset d := ⟨a, f, inferInstance⟩

lemma mk_eq (f : subset d) : @subset.mk _ _ _ _ f.ar f.mono = f := by
  rfl

variable (f g : subset d)

def subobject : Prop := ∃ h, h ≫ g.ar = f.ar
instance : HasSubset (subset d) := ⟨subobject⟩

instance isTrans : IsTrans (subset d) (· ⊆ ·) where
  trans := by
    rintro ⟨a, f⟩ ⟨b, g⟩ ⟨c, h⟩ ⟨i, hfg⟩ ⟨j, hgh⟩
    use i ≫ j
    rw [assoc, hgh, hfg]

def iso : Prop := f ⊆ g ∧ g ⊆ f

instance : HasEquiv (subset d) := ⟨iso⟩

instance iseqv : Equivalence <| iso (d := d) where
  refl := by
    rintro ⟨a, f, hf⟩
    constructor
    <;> use 𝟙 _
    <;> rw [id_comp]
  symm := by
    rintro ⟨a, f, hf⟩ ⟨b, g, hg⟩ ⟨hfg, hgf⟩
    constructor
    <;> assumption
  trans := by
    rintro ⟨a, f⟩ ⟨b, g⟩ ⟨c, h⟩ ⟨⟨i, hfg⟩, ⟨iinv, hgf⟩⟩ ⟨⟨j, hgh⟩, ⟨jinv, hhg⟩⟩
    constructor
    . use i ≫ j
      rw [assoc, hgh, hfg]
    use jinv ≫ iinv
    rw [assoc, hgf, hhg]

instance setoid : Setoid (subset d) where
  r := (· ≈ ·)
  iseqv := iseqv

end subset

lemma equiv_iso {a b d : 𝓒} {f : a ⟶ d} {g : b ⟶ d} [Mono f] [Mono g]
  {i : a ⟶ b} (hi : i ≫ g = f) {j : b ⟶ a} (hj : j ≫ f = g) : IsIso i ∧ IsIso j := by
  constructor
  . constructor
    use j
    constructor
    . apply cancel_mono f |>.mp
      rw [assoc, hj, hi, id_comp]
    apply cancel_mono g |>.mp
    rw [assoc, hi, hj, id_comp]
  use i
  constructor
  . apply cancel_mono g |>.mp
    rw [assoc, hi, hj, id_comp]
  . apply cancel_mono f |>.mp
    rw [assoc, hj, hi, id_comp]

def equiv_iso' {d : 𝓒} {f g : subset d}
    {i : f.dom ⟶ g.dom} (hi : i ≫ g.ar = f.ar) {j : g.dom ⟶ f.dom} (hj : j ≫ f.ar = g.ar)
    : f.dom ≅ g.dom := by
  have : Mono f.ar := f.mono
  have : Mono g.ar := g.mono
  have : IsIso i := equiv_iso hi hj |>.1
  apply asIso i

abbrev Sub (d : 𝓒) := Quotient (subset.setoid (d := d))

namespace Sub

variable (f g : Sub d)

def subobject : Prop := f.out ⊆ g.out
instance : HasSubset (Sub d) := ⟨subobject⟩

lemma sub_is_representative (f f' g g' : subset d)
  (hf: (⟦f⟧ : Sub d) = ⟦f'⟧) (hg : (⟦g⟧ : Sub d) = ⟦g'⟧)
  : f ⊆ g ↔ f' ⊆ g' := by
  have ⟨hff', hf'f⟩ := Quotient.exact hf
  have ⟨hgg', hg'g⟩ := Quotient.exact hg
  constructor
  . intro h
    apply hf'f.trans <| h.trans hgg'
  intro h
  apply hff'.trans <| h.trans hg'g

instance : PartialOrder (Sub d) where
  le := (· ⊆ ·)
  le_refl := by
    intro fs
    use 𝟙 _
    rw [id_comp]
  le_trans := by
    intro fs gs hs ⟨i, hfg⟩ ⟨j, hgh⟩
    use i ≫ j
    rw [assoc, hgh, hfg]
  lt_iff_le_not_le := by
    intro f g
    tauto
  le_antisymm := by
    intro fs gs hfg hgf
    rw [← Quotient.out_eq fs, ← Quotient.out_eq gs]
    apply Quotient.sound
    constructor
    . exact hfg
    exact hgf


end Sub

lemma subset.mk_out (f : subset d) : (⟦f⟧ : Sub d).out ≈ f := Quotient.mk_out f
section

variable {f g : subset d}

lemma Sub_subset_iff_subs : f ⊆ g ↔ (⟦f⟧ : Sub d) ⊆ ⟦g⟧ := by
  constructor
  . intro ⟨h, hh⟩
    have ⟨⟨p, hp⟩, _⟩ : ⟦f⟧.out ≈ f := f.mk_out
    have ⟨_, ⟨q, hq⟩⟩ : ⟦g⟧.out ≈ g := g.mk_out
    use p ≫ h ≫ q
    simp only [assoc]
    rw [hq, hh, hp]
  intro ⟨h, hh⟩
  have ⟨_, ⟨p, hp⟩⟩ : ⟦f⟧.out ≈ f := f.mk_out
  have ⟨⟨q, hq⟩, _⟩ : ⟦g⟧.out ≈ g := g.mk_out
  use p ≫ h ≫ q
  simp only [assoc]
  rw [hq, hh, hp]

lemma Sub_subset_iff_eqv : f ≈ g ↔ (⟦f⟧ : Sub d) = ⟦g⟧ := by
  constructor
  . apply Quotient.sound
  apply Quotient.exact

end

lemma subset_isIso {d : 𝓒} {f g : subset d} (h : f ≈ g) : ∃ _: IsIso h.1.choose, inv h.1.choose = h.2.choose := by
  have ⟨hp', hq'⟩ := h
  let p := hp'.choose
  let q := hq'.choose
  have hp := hp'.choose_spec
  have hq := hq'.choose_spec
  have : Mono f.ar := f.mono
  have : Mono g.ar := g.mono

  have : IsIso p := by
    constructor
    use q
    constructor
    . apply cancel_mono f.ar |>.mp
      rw [assoc, hq, hp, id_comp]
    apply cancel_mono g.ar |>.mp
    rw [assoc, hp, hq, id_comp]

  use this
  apply IsIso.inv_eq_of_hom_inv_id
  apply cancel_mono f.ar |>.mp
  rw [assoc, hq, hp, id_comp]

-- Elements

variable [HasTerminal 𝓒]

abbrev element (a : 𝓒) := ⊤_ 𝓒 ⟶ a

variable {a b : 𝓒}

lemma element.mono (x : element a) : Mono x := by
  apply «CH.3».«§3.6».Excercises.«3»

-- Naming arrows

variable [HasBinaryProducts 𝓒] [HasExponentials 𝓒]

abbrev name (f : a ⟶ b) : ⊤_ 𝓒 ⟶ a ⇨' b := exp.curry <| prod.fst ≫ f

theorem «Excrcise 2» (f : a ⟶ b) (x : element a) : prod.lift x (name f) ≫ exp.eval = x ≫ f := by
  symm
  calc
    x ≫ f
    _ = (prod.lift x (𝟙 _) ≫ prod.fst) ≫ f := by rw [prod.lift_fst]
    _ = prod.lift x (𝟙 _) ≫ prod.fst ≫ f := by rw [assoc]
    _ = prod.lift x (𝟙 _) ≫ prod.map (𝟙 _) (name f) ≫ exp.eval := by rw [← exp.uncurry, exp.fac' _]
    _ = prod.lift (x ≫ (𝟙 _)) (𝟙 _ ≫ (name f)) ≫ exp.eval := by rw [← assoc, prod.lift_map]
    _ = prod.lift x (name f) ≫ exp.eval := by rw [id_comp, comp_id]

end «§4.1»

namespace «§4.2»
-- Classifying subobjects

open «§4.1»

variable [HasTerminal 𝓒]

class HasSubobjectClassifier (Ω : 𝓒) where
  true : ⊤_ 𝓒 ⟶ Ω
  Ω_axiom {d : 𝓒} (f : subset d) : ∃! χ : d ⟶ Ω, IsPullback f.ar (terminal.from f.dom) χ true

lemma «§3.6 terminal_id» : terminal.from (⊤_ 𝓒) = 𝟙 _ := «CH.3».«§3.6».terminal_id 𝓒
lemma «§3.6.ex3» {a : 𝓒} (f : ⊤_ 𝓒 ⟶ a) : Mono f := «CH.3».«§3.6».Excercises.«3» 𝓒 f

lemma SubobjectClassifier.self_id {Ω : 𝓒} {χtrue : Ω ⟶ Ω} {true : ⊤_ 𝓒 ⟶ Ω}
    (huniq : ∀ (y : Ω ⟶ Ω), IsPullback true (terminal.from (⊤_ 𝓒)) y true → y = χtrue)
  : χtrue = 𝟙 _ := by
  have h1PB : IsPullback true (terminal.from (⊤_ 𝓒)) (𝟙 _) true := by
    constructor
    . constructor
      apply PullbackCone.IsLimit.mk (by rw [comp_id, «§3.6 terminal_id», id_comp]) (λ s ↦ terminal.from _)
      . intro s
        apply cancel_mono (𝟙 _) |>.mp
        rw [s.condition, comp_id]
        congr
        ext
      . intro s
        rw [terminal.comp_from]
        ext
      intro _ _ _ _
      ext
    constructor
    rw [comp_id, «§3.6 terminal_id», id_comp]
  rw [huniq (𝟙 _) h1PB]

def SubobjectClassifier.uniqueUpToIso {Ω Ω' : 𝓒} (t : HasSubobjectClassifier Ω) (t' : HasSubobjectClassifier Ω') : Ω ≅ Ω' := by
  let ts : subset Ω := ⟨_, t.true, «§3.6.ex3» _⟩
  let t's : subset Ω' := ⟨_, t'.true, «§3.6.ex3» _⟩
  let χt := (t.Ω_axiom t's).choose
  let χt' := (t'.Ω_axiom ts).choose
  have hPB : IsPullback t'.true (terminal.from _) χt t.true := (t.Ω_axiom t's).choose_spec.1
  have hPB' : IsPullback t.true (terminal.from _) χt' t'.true := (t'.Ω_axiom ts).choose_spec.1

  have oneEqId := terminal.hom_ext (terminal.from (⊤_ 𝓒)) (𝟙 _)

  have {Ω Ω' : 𝓒} {true : (⊤_ 𝓒) ⟶ Ω} {true' : (⊤_ 𝓒) ⟶ Ω'} {χt : Ω' ⟶ Ω} {χt' : Ω ⟶ Ω'}
      (hPB : IsPullback true' (terminal.from _) χt true)
      (hPB' : IsPullback true (terminal.from _) χt' true')
      (hself : ∃! χ : Ω ⟶ Ω, IsPullback true (terminal.from _) χ true)
    : χt' ≫ χt = 𝟙 _ := by
      have := IsPullback.paste_vert hPB' hPB
      rw [terminal.comp_from] at this
      have ⟨one, pb, huniq⟩ := hself
      rw [huniq (χt' ≫ χt) this, self_id huniq]
  apply show Ω ≅ Ω' from {
    hom := χt'
    inv := χt
    hom_inv_id := this hPB hPB' <| t.Ω_axiom ts
    inv_hom_id := this hPB' hPB <| t'.Ω_axiom t's
  }

lemma HasSubobjectClassifier.uniqueUpToIso' {Ω Ω' : 𝓒} (t : HasSubobjectClassifier Ω) (t' : HasSubobjectClassifier Ω')
    : ∃ h : IsIso (t.Ω_axiom (.mk t'.true)).choose, inv (t.Ω_axiom (.mk t'.true)).choose = (t'.Ω_axiom (.mk t.true)).choose := by
  let ts : subset Ω := .mk t.true
  let t's : subset Ω' := .mk t'.true
  let χt := (t.Ω_axiom t's).choose
  let χt' := (t'.Ω_axiom ts).choose
  have hPB : IsPullback t'.true (terminal.from _) χt t.true := (t.Ω_axiom t's).choose_spec.1
  have hPB' : IsPullback t.true (terminal.from _) χt' t'.true := (t'.Ω_axiom ts).choose_spec.1

  have oneEqId := terminal.hom_ext (terminal.from (⊤_ 𝓒)) (𝟙 _)
  have h₁ {Ω Ω' : 𝓒} {true : (⊤_ 𝓒) ⟶ Ω} {true' : (⊤_ 𝓒) ⟶ Ω'} {χt : Ω' ⟶ Ω} {χt' : Ω ⟶ Ω'}
      (hPB : IsPullback true' (terminal.from _) χt true)
      (hPB' : IsPullback true (terminal.from _) χt' true')
      (hself : ∃! χ : Ω ⟶ Ω, IsPullback true (terminal.from _) χ true)
    : χt' ≫ χt = 𝟙 _ := by
      have := IsPullback.paste_vert hPB' hPB
      rw [terminal.comp_from] at this
      have ⟨one, pb, huniq⟩ := hself
      rw [huniq (χt' ≫ χt) this, SubobjectClassifier.self_id huniq]

  let h : Ω' ≅ Ω := {
    hom := χt
    inv := χt'
    hom_inv_id := h₁ hPB' hPB <| t'.Ω_axiom t's
    inv_hom_id := h₁ hPB hPB' <| t.Ω_axiom ts
  }

  have : IsIso χt := by
    apply h.isIso_hom
  use this
  apply IsIso.inv_eq_of_hom_inv_id
  apply h₁ hPB' hPB <| t'.Ω_axiom t's

class IsSubobjectClassifier {Ω : 𝓒} (true : ⊤_ 𝓒 ⟶ Ω) where
  Ω_axiom {d : 𝓒} (f : subset d) : ∃! χ : d ⟶ Ω, IsPullback f.ar (terminal.from f.dom) χ true

def IsSubobjectClassifier.hasSubobjectClassifier {Ω : 𝓒} {true : ⊤_ 𝓒 ⟶ Ω}
    (i : IsSubobjectClassifier true) : HasSubobjectClassifier Ω where
  true := true
  Ω_axiom := i.Ω_axiom

def HasSubobjectClassifier.isSubobjectClassifier {Ω : 𝓒} (t : HasSubobjectClassifier Ω)
    : IsSubobjectClassifier t.true where
  Ω_axiom := t.Ω_axiom

variable {Ω : 𝓒} [HasSubobjectClassifier Ω]

section
variable {a d : 𝓒} (f : subset d)

abbrev true : ⊤_ 𝓒 ⟶ Ω := HasSubobjectClassifier.true
lemma true.mono : Mono <| true (Ω := Ω) := «§3.6.ex3» _

abbrev χ : d ⟶ Ω := (HasSubobjectClassifier.Ω_axiom f).choose

def χ.spec :
    IsPullback f.ar (terminal.from f.dom) (χ f) (true (Ω := Ω)) ∧
    ∀ (y : d ⟶ Ω), IsPullback f.ar (terminal.from f.dom) y true → y = χ f := by
  apply (HasSubobjectClassifier.Ω_axiom f).choose_spec

end

lemma χ.Sub_subset {d : 𝓒} (f : subset d) (χf : d ⟶ Ω) (true : ⊤_ 𝓒 ⟶ Ω)
    (h : IsPullback f.ar (terminal.from _) χf true)
    : IsPullback (⟦f⟧ : Sub d).out.ar (terminal.from _) χf true := by
  have heqv : (⟦f⟧ : Sub d).out ≈ f := f.mk_out
  let p := heqv.1.choose
  let q := heqv.2.choose
  have ⟨hp, hpq⟩ : ∃ _: IsIso p, inv p = q := subset_isIso heqv

  apply h.of_iso (asIso p).symm (.refl _) (.refl _) (.refl _)
    (by dsimp; rw [comp_id, hpq, heqv.2.choose_spec]) (by simp) (by simp) (by simp)


theorem «Theorem» {d : 𝓒} (f g : subset d) :
    f ≈ g ↔ χ f (Ω := Ω) = χ g := by
  constructor
  . rintro ⟨⟨kinv, hkinv⟩, ⟨k, hk⟩⟩
    have ⟨hfPB, _⟩ := χ.spec f (Ω := Ω)
    have ⟨_, hguniq⟩ := χ.spec g (Ω := Ω)
    apply hguniq
    rw [← hk]
    constructor
    . constructor
      apply PullbackCone.IsLimit.mk (by rw [assoc, hfPB.w, ← assoc, terminal.comp_from]) (λ s ↦ (hfPB.lift s.fst s.snd s.condition) ≫ kinv)
      . intro s
        rw [assoc, hk, hkinv, hfPB.lift_fst]
      . intro s
        rw [terminal.comp_from]
        ext
      intro s m hmfst _
      rw [hk] at hmfst
      have : Mono g.ar := g.mono
      apply cancel_mono g.ar |>.mp
      rw [assoc, hkinv, hfPB.lift_fst, hmfst]
    constructor
    rw [assoc, hfPB.w, ← assoc, terminal.comp_from]
  intro heq
  have ⟨hfPB, _⟩ := χ.spec f (Ω := Ω)
  have ⟨hgPB, _⟩ := χ.spec g (Ω := Ω)
  constructor
  . let h := hgPB.lift f.ar (terminal.from _) <| heq.symm ▸ hfPB.w
    use h
    rw [hgPB.lift_fst]
  let k := hfPB.lift g.ar (terminal.from _) <| heq ▸ hgPB.w
  use k
  rw [hfPB.lift_fst]

namespace rf
variable {d : 𝓒} (h : d ⟶ Ω) [HasPullbacks 𝓒]

abbrev a : 𝓒 := pullback h true
abbrev f : a h ⟶ d := pullback.fst h true
lemma f.PB : IsPullback (f h) (terminal.from _) h true := by
  have : terminal.from _ = pullback.snd h true := by ext
  rw [this]
  apply IsPullback.of_isLimit <| pullbackIsPullback h true
lemma f.mono : Mono (f h) := by
  apply «CH.3».«§3.13».Exercise _ _ _ _ _ (f.PB h).flip true.mono
abbrev subset_f : subset d := ⟨a h, f h, f.mono h⟩
lemma subset_f.eq : h = χ (subset_f h) := by
  have ⟨hPB, huniq⟩ := χ.spec (subset_f h) (Ω := Ω)
  apply huniq h
  dsimp [subset.dom, subset.ar]
  apply f.PB

end rf

lemma χ.sub_out_eq_subset {d : 𝓒} (f : subset d) : χ (⟦f⟧ : Sub d).out = χ f (Ω := Ω) := by
  apply «CH.4».«§4.2».Theorem _ _ (Ω := Ω) |>.mp
  apply f.mk_out

theorem «Exercise 1» : χ (.mk true) = 𝟙 Ω := by
  have ⟨_, huniq⟩ := χ.spec (Ω := Ω) <| .mk (true (Ω := Ω))
  apply SubobjectClassifier.self_id huniq

lemma id_mono {a : 𝓒} : Mono (𝟙 a) := by
  constructor
  intro X f g h
  simp only [comp_id] at h
  apply h

abbrev true' (a : 𝓒) : a ⟶ Ω := terminal.from _ ≫ true

theorem «Exercise 2» : χ (.mk (𝟙 Ω)) = true' Ω (Ω := Ω) := by
  have ⟨hPB, huniq⟩ := χ.spec (.mk (𝟙 Ω)) (Ω := Ω)
  symm
  apply huniq
  constructor
  . constructor
    apply PullbackCone.IsLimit.mk (by rw [id_comp]) (λ s ↦ s.fst)
    . intro s
      rw [comp_id]
    . intro s
      rw [terminal.comp_from]
      ext
    intro _ _ hmfst _
    rw [comp_id] at hmfst
    apply hmfst
  constructor
  rw [id_comp]

-- 7章でちょいちょい使うため
lemma «Exercise 2'» [HasPullbacks 𝓒] : χ (.mk (𝟙 _)) = true (Ω := Ω) := by
  symm
  have ⟨hPB, huniq⟩ := χ.spec (.mk (𝟙 (⊤_ 𝓒))) (Ω := Ω)
  apply huniq
  rw [«CH.3».«§3.6».terminal_id]
  apply «CH.3».«§3.13».«Example 9» _ true |>.mp true.mono

lemma «Exercise 2''» {d : 𝓒} : χ (.mk (𝟙 d)) = true' d (Ω := Ω) := by
  symm
  have ⟨hPB, huniq⟩ := χ.spec (.mk (𝟙 d)) (Ω := Ω)
  apply huniq
  dsimp [subset.ar, subset.dom]
  constructor
  . constructor
    apply PullbackCone.IsLimit.mk (by rw [id_comp]) (λ s ↦ s.fst)
    . intro s; simp
    . intro s; ext
    intro _ _ hmfst _
    rw [comp_id] at hmfst
    apply hmfst
  constructor
  rw [id_comp]

theorem «Exercise 3» {a b : 𝓒} (f : a ⟶ b) : f ≫ true' b = true' a (Ω := Ω) := by
  rw [← assoc]
  congr
  rw [terminal.comp_from]

end «§4.2»

namespace «§4.3»
-- Definition of Topos

open «§4.2»

variable (Ω : 𝓒)

open «CH.3».«§3.15» «§4.2» in
class ElementaryTopos (Ω : semiOutParam 𝓒) where
  «(1)» : HasLimits 𝓒
  «(2)» : HasColimits 𝓒
  -- NOTE: (3)のために必要だけど自動で導出するようにしたい
  has_binary_product : HasBinaryProducts 𝓒 := by apply «(1)»
  «(3)» : HasExponentials 𝓒
  has_terminal : HasTerminal 𝓒 := by apply «(1)»
  «(4)» : HasSubobjectClassifier Ω

def ElementaryTopos.byCC
    («(1').1» : HasTerminal 𝓒)
    («(1').2» : HasPullbacks 𝓒)
    («(1').3» : HasBinaryProducts 𝓒)
    («(2').1» : HasInitial 𝓒)
    («(2').2» : HasPushouts 𝓒)
    («(3)» : HasExponentials 𝓒)
    («(4)» : HasSubobjectClassifier Ω)
  : ElementaryTopos Ω where
    «(1)» := «CH.3».«§3.15».«Theorem 1» 𝓒
    «(2)» := «CH.3».«§3.15».«Theorem 1'» 𝓒
    «(3)» := «(3)»
    «(4)» := «(4)»
    has_binary_product := «(1').3»
    has_terminal := «(1').1»

-- cf. Pare[74]
open «CH.3».«§3.15» in
axiom finitelyCoCompleteFromOther
    («(1)» : HasLimits 𝓒)
    («(1').3» : HasBinaryProducts 𝓒)
    («(3)» : HasExponentials 𝓒)
    («(1').1» : HasTerminal 𝓒)
    («(4)» : HasSubobjectClassifier Ω)
  : HasColimits 𝓒

def ElementaryTopos.byCC_SC
    (cc : «CH.3».«§3.16».CartesianClosed 𝓒)
    («(1').1» : HasTerminal 𝓒)
    (t : HasSubobjectClassifier Ω)
  : ElementaryTopos Ω where
    «(1)» := cc.finite_complete
    «(2)» := finitelyCoCompleteFromOther Ω cc.finite_complete cc.has_binary_products cc.has_exponentials «(1').1» t
    has_binary_product := cc.has_binary_products
    «(3)» := cc.has_exponentials
    has_terminal := «(1').1»
    «(4)» := t

variable [ElementaryTopos Ω]

instance ElementaryTopos.hasLimits : HasLimits 𝓒 := by
  apply ElementaryTopos.«(1)» Ω
instance ElementaryTopos.hasColimits : HasColimits 𝓒 := by
  apply ElementaryTopos.«(2)» Ω
instance ElementaryTopos.hasExponentials : HasExponentials 𝓒 := by
  apply @ElementaryTopos.«(3)» 𝓒 _ Ω
instance ElementaryTopos.hasSubobjectClassifier : HasSubobjectClassifier Ω := by
  apply @ElementaryTopos.«(4)» 𝓒 _ Ω
instance ElementaryTopos.ccc : «CH.3».«§3.16».CartesianClosed 𝓒 := by
  sorry

end «§4.3»

namespace «§4.7»
-- Power objects

open «§4.2»

variable [HasBinaryProducts 𝓒]

structure PowerObject (a : 𝓒) where
  𝓟a : 𝓒
  containOb : 𝓒
  containHom : containOb ⟶ a ⨯ 𝓟a
  monoCH : Mono containHom
  property : ∀ (b : 𝓒) (R : 𝓒)
    (r : R ⟶ a ⨯ b) [Mono r],
    ∃! (fᵣ : b ⟶ 𝓟a), ∃ (t : R ⟶ containOb),
    (h : Mono fᵣ) →  IsPullback r t (prod.map (𝟙 a) fᵣ) containHom

variable (𝓒)
abbrev HasPowerObject : Prop := ∀ (a : 𝓒), Nonempty (PowerObject a)
variable {𝓒}

variable [HasTerminal 𝓒] [HasExponentials 𝓒]

theorem «Theorem 1» {Ω : 𝓒} [HasSubobjectClassifier Ω] : HasPowerObject 𝓒 := by
  intro a
  let 𝓟a := a ⇨' Ω
  let ev : a ⨯ a ⇨' Ω ⟶ Ω := exp.eval
  let cOb := rf.a ev
  let CHom := rf.f ev
  let hmono := rf.f.mono ev
  have hPB := rf.f.PB ev
  constructor
  apply show PowerObject a from {
    𝓟a := 𝓟a
    containOb := cOb
    containHom := CHom
    monoCH := hmono
    property := by
      intro b R r hr
      let χr : a ⨯ b ⟶ Ω := χ (.mk r)
      let fr : b ⟶ a ⇨' Ω := exp.curry χr
      let ofe := prod.map (𝟙 a) fr ≫ ev
      let R' := rf.a ofe
      let r' := rf.f ofe
      have rmono : Mono r' := rf.f.mono ofe
      have rPB := rf.f.PB ofe
      -- let u : R' ⟶ cOb := hPB.lift (r' ≫ prod.map (𝟙 _) fr) (terminal.from _) (by
      --   have := rPB.w
      --   dsimp [ofe] at this
      --   simp [rPB.w])
      -- have hu : u ≫ terminal.from _ = terminal.from _ := hPB.lift_snd (r' ≫ prod.map (𝟙 _) fr) (terminal.from _) (by simp [rPB.w])
      -- rw [← hu] at rPB
      -- have := IsPullback.of_bot rPB (by sorry) hPB
      -- TODO: RとR'が同じであることを証明しないといけないけど出来る？
      -- TODO: frのMono条件が示せない？
      sorry
  }

end «§4.7»

namespace «§4.8»
-- Ω and comprehensions

open «§4.1» «§4.2»

variable [HasTerminal 𝓒]

def catElemMembership {b : 𝓒} (f : subset b) (x : element b) : Prop
  := ∃ k : element f.dom, k ≫ f.ar = x

instance {b : 𝓒} : Membership (element b) (subset b) where
  mem := catElemMembership

lemma «Exercise 1» {b : 𝓒} (f g : subset b) (h : f ⊆ g) (x : element b) : x ∈ f → x ∈ g := by
  intro ⟨k, hk⟩
  have ⟨i, hi⟩ := h
  use k ≫ i
  rw [assoc, hi, hk]

variable {Ω : 𝓒} [«§4.3».ElementaryTopos Ω]

lemma «Exercise 2» {d : 𝓒} (f : subset d) (x : element d)
    : x ∈ f ↔ x ≫ χ f = «§4.2».true (Ω := Ω) := by
  have ⟨h, _⟩ := χ.spec f (Ω := Ω)
  have : terminal.from (⊤_ 𝓒) = 𝟙 (⊤_ 𝓒) := by ext
  constructor
  . intro ⟨k, hk⟩
    rw [← hk, assoc, h.w, ← assoc, terminal.comp_from, this, id_comp]
  intro he
  let k := h.lift x (terminal.from _) (by rw [he, this, id_comp])
  use k
  rw [h.lift_fst]
