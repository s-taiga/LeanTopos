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

variable  {a b c d : 𝓒} {f : a ⟶ d} {g : b ⟶ d} {k : c ⟶ d} [Mono f] [Mono g] [Mono k]

def subobject (f : a ⟶ d) (g : b ⟶ d) : Prop := ∃ h: a ⟶ b, h ≫ g = f

infix:60 " ⊆ₛ " => subobject

lemma «(i) reflective» : f ⊆ₛ f := by
  use 𝟙 _
  rw [id_comp]

lemma «(ii) transitive» : f ⊆ₛ g → g ⊆ₛ k → f ⊆ₛ k := by
  rintro ⟨h, hh⟩ ⟨i, hi⟩
  use h ≫ i
  rw [assoc, hi, hh]

def «isomorphic subobjects» (f : a ⟶ d) (g : b ⟶ d) : Prop := f ⊆ₛ g ∧ g ⊆ₛ f

infix:60 " ≃ₛ " => «isomorphic subobjects»

lemma refl : f ≃ₛ f := by
  constructor <;> apply «(i) reflective»
lemma symm : f ≃ₛ g → g ≃ₛ f := by
  rintro ⟨hfg, hgf⟩
  constructor <;> assumption
lemma trans : f ≃ₛ g → g ≃ₛ k → f ≃ₛ k := by
  rintro ⟨hfg, hgf⟩ ⟨hgk, hkg⟩
  constructor
  . apply «(ii) transitive» hfg hgk
  apply «(ii) transitive» hkg hgf

def Subs (d : 𝓒) := Σ' (a : 𝓒) (f : a ⟶ d), Mono f

def subobject' {d : 𝓒} (f g : Subs d) : Prop := ∃ h, h ≫ g.2.1 = f.2.1

infix:60 " ⊆ₛ' " => subobject'

def Subs.iso (f g : Subs d) : Prop := f ⊆ₛ' g ∧ g ⊆ₛ' f

infix:60 " ≃ₛ' " => Subs.iso

def Subs.eqv {d : 𝓒} : Equivalence (Subs.iso (d := d)) where
  refl := by
    rintro ⟨a, f⟩
    constructor
    <;> use 𝟙 _
    <;> rw [id_comp]
  symm := by
    rintro ⟨a, f⟩ ⟨b, g⟩ ⟨hfg, hgf⟩
    constructor
    <;> assumption
  trans := by
    rintro ⟨a, f⟩ ⟨b, g⟩ ⟨c, h⟩ ⟨⟨i, hfg⟩, ⟨iinv, hgf⟩⟩ ⟨⟨j, hgh⟩, ⟨jinv, hhg⟩⟩
    constructor
    . use i ≫ j
      rw [assoc, hgh, hfg]
    use jinv ≫ iinv
    rw [assoc, hgf, hhg]

def Subs.setoid (d : 𝓒) : Setoid (Subs d) where
  r := Subs.iso (d := d)
  iseqv := eqv

def subs (f : a ⟶ d) {hf : Mono f} : Subs d := ⟨a, f, hf⟩

def Subs.cls (f : Subs d) := {g // f ≃ₛ' g}

-- Elements

variable [HasTerminal 𝓒]

abbrev element (a : 𝓒) := ⊤_ 𝓒 ⟶ a

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

variable [HasTerminal 𝓒]

class HasSubobjectClassifier (Ω : 𝓒) where
  true : ⊤_ 𝓒 ⟶ Ω
  Ω_axiom {a d : 𝓒} : ∀ f : a ⟶ d, Mono f → ∃! χ : d ⟶ Ω, IsPullback f (terminal.from a) χ true

-- TODO: «CH.3».«§3.6».terminal_idと同じ内容なのでまとめる
lemma terminal.fromTiso1 [HasTerminal 𝓒]: terminal.from (⊤_ 𝓒) = 𝟙 _ := terminal.hom_ext (terminal.from (⊤_ 𝓒)) _

lemma SubobjectClassifier.self_id {Ω : 𝓒} {χtrue : Ω ⟶ Ω} {true : ⊤_ 𝓒 ⟶ Ω}
    (huniq : ∀ (y : Ω ⟶ Ω), IsPullback true (terminal.from (⊤_ 𝓒)) y true → y = χtrue)
  : χtrue = 𝟙 _ := by
  have h1PB : IsPullback true (terminal.from (⊤_ 𝓒)) (𝟙 _) true := by
    constructor
    . constructor
      apply PullbackCone.IsLimit.mk (by rw [comp_id, terminal.fromTiso1, id_comp]) (λ s ↦ terminal.from _)
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
    rw [comp_id, terminal.fromTiso1, id_comp]
  rw [huniq (𝟙 _) h1PB]

lemma «§3.6.ex3» {a : 𝓒} (f : ⊤_ 𝓒 ⟶ a) : Mono f := «CH.3».«§3.6».Excercises.«3» 𝓒 f

def SubobjectClassifier.uniqueUpToIso {Ω Ω' : 𝓒} (t : HasSubobjectClassifier Ω) (t' : HasSubobjectClassifier Ω') : Nonempty (Ω ≅ Ω') := by
  let ⟨χt, hPB, _⟩ := t.Ω_axiom  t'.true («§3.6.ex3» t'.true)
  let ⟨χt', hPB', _⟩ := t'.Ω_axiom  t.true («§3.6.ex3» t.true)

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
  constructor
  apply show Ω ≅ Ω' from {
    hom := χt'
    inv := χt
    hom_inv_id := this hPB hPB' <| t.Ω_axiom t.true («§3.6.ex3» t.true)
    inv_hom_id := this hPB' hPB <| t'.Ω_axiom t'.true («§3.6.ex3» t'.true)
  }

section

variable {Ω a d : 𝓒} [HasSubobjectClassifier Ω] (f : a ⟶ d) (hf : Mono f)

abbrev true : ⊤_ 𝓒 ⟶ Ω := HasSubobjectClassifier.true

abbrev χ : d ⟶ Ω := (HasSubobjectClassifier.Ω_axiom f hf).choose

def χ.spec : IsPullback f (terminal.from a) (χ f hf) (true (Ω := Ω)) ∧ ∀ (y : d ⟶ Ω), IsPullback f (terminal.from a) y true → y = χ f hf := by
  apply (HasSubobjectClassifier.Ω_axiom f hf).choose_spec

-- TODO: SubobjectClassifierの定義の見直しが必要かも
lemma Ω_axiom' : ∀ χ : d ⟶ Ω, ∃ (a : 𝓒), ∃! (f : a ⟶ d), Mono f ∧ IsPullback f (terminal.from a) χ true := by
  intro χ'
  sorry

end

open «§4.1»

variable {Ω : 𝓒} [HasSubobjectClassifier Ω]

theorem «Theorem» {a b d : 𝓒} (f : a ⟶ d) (hf : Mono f) (g : b ⟶ d) (hg : Mono g) :
    f ≃ₛ g ↔ χ f hf = χ g hg (Ω := Ω) := by
  constructor
  . rintro ⟨⟨kinv, hkinv⟩, ⟨k, hk⟩⟩
    have ⟨hfPB, _⟩ := χ.spec f hf (Ω := Ω)
    have ⟨_, hguniq⟩ := χ.spec g hg (Ω := Ω)
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
      apply cancel_mono g |>.mp
      rw [assoc, hkinv, hfPB.lift_fst, hmfst]
    constructor
    rw [assoc, hfPB.w, ← assoc, terminal.comp_from]
  intro heq
  have ⟨hfPB, _⟩ := χ.spec f hf (Ω := Ω)
  have ⟨hgPB, _⟩ := χ.spec g hg (Ω := Ω)
  constructor
  . let h := hgPB.lift f (terminal.from _) <| heq.symm ▸ hfPB.w
    use h
    rw [hgPB.lift_fst]
  let k := hfPB.lift g (terminal.from _) <| heq ▸ hgPB.w
  use k
  rw [hfPB.lift_fst]

theorem «Exercise 1» : χ true («§3.6.ex3» true) = 𝟙 Ω := by
  have ⟨_, huniq⟩ := χ.spec (Ω := Ω) (true (Ω := Ω)) («§3.6.ex3» true)
  apply SubobjectClassifier.self_id huniq

lemma id_mono {a : 𝓒} : Mono (𝟙 a) := by
  constructor
  intro X f g h
  simp only [comp_id] at h
  apply h

abbrev true' (a : 𝓒) : a ⟶ Ω := terminal.from _ ≫ true

theorem «Exercise 2» : χ (𝟙 Ω) id_mono = true' Ω (Ω := Ω) := by
  have ⟨hPB, huniq⟩ := χ.spec (𝟙 Ω) id_mono (Ω := Ω)
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
class ElementaryTopos where
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
lemma finitelyCoCompleteFromOther
    («(1)» : HasLimits 𝓒)
    («(1').3» : HasBinaryProducts 𝓒)
    («(3)» : HasExponentials 𝓒)
    («(1').1» : HasTerminal 𝓒)
    («(4)» : HasSubobjectClassifier Ω)
  : HasColimits 𝓒 := by sorry

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
  -- apply @ElementaryTopos.«(1)» 𝓒 _ Ω
  sorry
instance ElementaryTopos.hasColimits : HasColimits 𝓒 := by
  -- apply @ElementaryTopos.«(2)» 𝓒 _ Ω
  sorry
instance ElementaryTopos.hasExponentials : HasExponentials 𝓒 := by
  -- apply @ElementaryTopos.«(3)» 𝓒 _ Ω
  sorry
instance ElementaryTopos.hasSubobjectClassifier : HasSubobjectClassifier Ω := by
  -- apply @ElementaryTopos.«(4)» 𝓒 _ Ω
  sorry
instance ElementaryTopos.ccc : «CH.3».«§3.16».CartesianClosed 𝓒 := by
  sorry

end «§4.3»

namespace «§4.4»
-- First examples

open «CH.3».«§3.16»

namespace «Example 1»
-- NOTE: 教科書だとSetの圏にしているが、大変だったのですでに定義されているType uの圏に対して各種極限を定義

instance types.hasTerminal : HasTerminal (Type u) := by
  apply IsTerminal.hasTerminal (X := PUnit)
  apply IsTerminal.ofUniqueHom (λ X x ↦ .unit)
  intro X f
  ext

instance : HasPullbacks (Type u) := by
  have {X Y Z : Type u} {f : X ⟶ Z} {g : Y ⟶ Z}: HasLimit (cospan f g) := by
    apply HasLimit.mk
    apply show LimitCone (cospan f g) from {
      cone := PullbackCone.mk (W := {w : X × Y // f w.1 = g w.2}) (λ w ↦ Prod.fst w.val) (λ w ↦ Prod.snd w.val) (by
        dsimp [types_comp]
        ext ⟨⟨x, y⟩, h⟩
        dsimp
        apply h
      )
      isLimit := PullbackCone.IsLimit.mk _ (λ s w ↦ ⟨⟨s.fst w, s.snd w⟩, by
        have := s.condition
        simp only [types_comp] at this
        dsimp
        rw [← Function.comp_apply (f := f), this]
        dsimp⟩)
        (by intro s; ext w; dsimp)
        (by intro s; ext w; dsimp) (by
        intro s m hmfst hmsnd
        ext w
        . dsimp
          rw [← hmfst]
          dsimp
        dsimp
        rw [← hmsnd]
        dsimp
      )
    }
  apply hasPullbacks_of_hasLimit_cospan

instance types.hasBinaryProducts : HasBinaryProducts (Type u) := by
  have {X Y : Type u}: HasLimit (pair X Y) := by
    apply HasLimit.mk {
      cone := Types.binaryProductCone X Y
      isLimit := Types.binaryProductLimit X Y
    }
  apply hasBinaryProducts_of_hasLimit_pair

abbrev types.p2p {a b : Type u} : (a ⨯ b) ≅ (a × b) := Types.binaryProductIso a b

-- TODO: prod A B と Prod A B が同じであることを示す
instance types.hasExponentials : HasExponentials (Type u) := by
  intro X Y
  apply HasPLimit.mk
  apply show PLimitCone (ones Y) X from {
    cone := ExpFan.mk (c := X → Y) (λ w ↦ ((p2p.hom ≫ Prod.snd) w) ((p2p.hom ≫ Prod.fst) w))
    isPLimit := ExpFan.IsPLimit.mk
      (λ s w x ↦ s.eval <| p2p.inv ⟨x, w⟩)
      (by
      intro s
      ext x
      simp only [p2p]
      rw [Types.binaryProductIso_hom_comp_snd X _, Types.binaryProductIso_hom_comp_fst X _]
      dsimp
      sorry)
      (by sorry)
  }

instance types.CC : CartesianClosed (Type u) where
  finite_complete := «CH.3».«§3.15».«Theorem 1» (Type u)
  has_binary_products := types.hasBinaryProducts
  has_exponentials := types.hasExponentials

-- TODO: χ の定義ができない
instance types.subobjectClassifier : «§4.2».HasSubobjectClassifier Bool where
  true := λ _ ↦ true
  Ω_axiom := by
    intro a b f hf
    -- let χ : b ⟶ Bool := λ b ↦
    --   if b ∈ f '' Set.univ then
    --     true
    --   else
    --     false
    sorry

instance types.ET : «§4.3».ElementaryTopos Bool :=
  .byCC_SC Bool CC hasTerminal subobjectClassifier

end «Example 1»

namespace «Example 4»
-- NOTE: 教科書だとSetのペアにしているが、大変なのでトポスである圏のペアを考える

open «§4.3»

instance : Category (𝓒 × 𝓒) := CategoryTheory.prod 𝓒 𝓒

variable (Ω : 𝓒) [ElementaryTopos Ω]
  [HasTerminal 𝓒] [HasPullbacks 𝓒] [HasBinaryProducts 𝓒] [HasExponentials 𝓒]

instance pair.hasTerminal : HasTerminal (𝓒 × 𝓒) := by
  apply IsTerminal.hasTerminal (X := (⊤_ 𝓒, ⊤_ 𝓒))
  apply IsTerminal.ofUniqueHom (λ X ↦ (terminal.from X.1, terminal.from X.2))
  intro X f
  ext

instance : HasPullbacks (𝓒 × 𝓒) := by
  have {AB CD EF : 𝓒 × 𝓒} {fg : AB ⟶ EF} {hk : CD ⟶ EF}: HasLimit (cospan fg hk) := by
    apply HasLimit.mk
    apply show LimitCone (cospan fg hk) from {
      cone := PullbackCone.mk (f := fg) (g := hk)
        (W := (pullback fg.1 hk.1, pullback fg.2 hk.2))
        (pullback.fst fg.1 hk.1, pullback.fst fg.2 hk.2)
        (pullback.snd fg.1 hk.1, pullback.snd fg.2 hk.2)
        (by ext <;> dsimp <;> rw [pullback.condition])
      isLimit := PullbackCone.IsLimit.mk
        (by ext <;> dsimp <;> rw [pullback.condition])
        (λ s ↦ (
          pullback.lift s.fst.1 s.snd.1 (Prod.eq_iff_fst_eq_snd_eq.mp s.condition |>.1),
          pullback.lift s.fst.2 s.snd.2 (Prod.eq_iff_fst_eq_snd_eq.mp s.condition |>.2)))
        (by intro s; ext <;> apply pullback.lift_fst)
        (by intro s; ext <;> apply pullback.lift_snd)
        (by
        intro s m hmfst hmsnd
        have ⟨hmf₁, hmf₂⟩ := Prod.eq_iff_fst_eq_snd_eq.mp hmfst
        have ⟨hms₁, hms₂⟩ := Prod.eq_iff_fst_eq_snd_eq.mp hmsnd
        dsimp at hmf₁ hmf₂ hms₁ hms₂
        ext
        . rw [pullback.lift_fst, hmf₁]
        . rw [pullback.lift_snd, hms₁]
        . rw [pullback.lift_fst, hmf₂]
        rw [pullback.lift_snd, hms₂]
        )
    }
  apply hasPullbacks_of_hasLimit_cospan

instance pair.hasBinaryProducts : HasBinaryProducts (𝓒 × 𝓒) := by
  have {AB CD : 𝓒 × 𝓒} : HasLimit (pair AB CD) := by
    set A := AB.1
    set B := AB.2
    set C := CD.1
    set D := CD.2
    apply HasLimit.mk {
      cone := BinaryFan.mk (P := (A ⨯ C, B ⨯ D)) (prod.fst, prod.fst) (prod.snd, prod.snd)
      isLimit := BinaryFan.isLimitMk
        (λ s ↦ (prod.lift s.fst.1 s.snd.1, prod.lift s.fst.2 s.snd.2))
        (by intro s; ext <;> dsimp <;> rw [prod.lift_fst])
        (by intro s; ext <;> dsimp <;> rw [prod.lift_snd])
        (by
        intro s h hmfst hmsnd
        have ⟨hmf₁, hmf₂⟩ := Prod.eq_iff_fst_eq_snd_eq.mp hmfst
        have ⟨hms₁, hms₂⟩ := Prod.eq_iff_fst_eq_snd_eq.mp hmsnd
        dsimp at hmf₁ hmf₂ hms₁ hms₂
        ext
        . rw [prod.lift_fst, hmf₁]
        . rw [prod.lift_snd, hms₁]
        . rw [prod.lift_fst, hmf₂]
        rw [prod.lift_snd, hms₂]
        )
    }
  apply hasBinaryProducts_of_hasLimit_pair

lemma prodIsProd {ab cd : 𝓒 × 𝓒} : (ab ⨯ cd) = (ab.1 ⨯ cd.1, ab.2 ⨯ cd.2) := sorry
lemma prodFst {a b c d : 𝓒} : ((a, c) ⨯ (b, d)).1 = (a ⨯ b) := by rw [prodIsProd]
lemma prodSnd {a b c d : 𝓒} : ((a, c) ⨯ (b, d)).2 = (c ⨯ d) := by rw [prodIsProd]

instance pair.hasExponentials : HasExponentials (𝓒 × 𝓒) := by
  rintro ⟨A, B⟩ ⟨C, D⟩
  sorry
  -- NOTE: prodIsProd内容が使えないため定義できない
  -- apply HasPLimit.mk (show PLimitCone (ones (C, D)) (A, B) from {
  --   cone := ExpFan.mk (exp.eval, exp.eval)
  --   isPLimit := ExpFan.IsPLimit.mk
  --     (λ s ↦
  --     let y : A ⨯ s.pt.1 ⟶ C := s.eval.1
  --     (exp.curry s.eval.1, exp.curry s.eval.2))
  --     (by sorry)
  --     (by sorry)
  -- })

end «Example 4»

namespace «Example 5»

instance : Category (Arrow 𝓒) := commaCategory

variable [HasTerminal 𝓒]

instance arrow.hasTerminal : HasTerminal (Arrow 𝓒) := by
  apply IsTerminal.hasTerminal (X := Arrow.mk (𝟙 (⊤_ 𝓒)))
  apply IsTerminal.ofUniqueHom
    (λ X ↦ Arrow.homMk
      (u := terminal.from X.left)
      (v := terminal.from X.right)
      (by dsimp; rw [comp_id, terminal.comp_from]))
  intro X f
  ext
  <;> dsimp
  <;> ext

variable [HasPullbacks 𝓒]

instance : HasPullbacks (Arrow 𝓒) := by
  have {AB CD EF : Arrow 𝓒} {ij : AB ⟶ EF} {pq : CD ⟶ EF}: HasLimit (cospan ij pq) := by
  -- NOTE: 対象が多く、ややこしかったので教科書の図に出てくる対象と射の名前を列挙した
    let A := AB.left
    let B := AB.right
    let C := CD.left
    let D := CD.right
    let E := EF.left
    let F := EF.right
    let i : A ⟶ E := ij.left
    let j : B ⟶ F := ij.right
    let p : C ⟶ E := pq.left
    let q : D ⟶ F := pq.right
    let f : A ⟶ B := AB.hom
    let g : E ⟶ F := EF.hom
    let h : C ⟶ D := CD.hom
    set P := pullback i p
    set Q := pullback j q
    let u : P ⟶ A := pullback.fst i p
    let r : P ⟶ C := pullback.snd i p
    let v : Q ⟶ B := pullback.fst j q
    let s : Q ⟶ D := pullback.snd j q
    let pcon : u ≫ i = r ≫ p := (pullback.cone i p).condition
    let k : P ⟶ Q := pullback.lift (f := j) (g := q) (u ≫ f) (r ≫ h) (by
        simp only [assoc]
        have fw : i ≫ g = f ≫ j := ij.w
        have gw : p ≫ g = h ≫ q := pq.w
        rw [← fw, ← gw]
        simp only [← assoc]
        rw [pcon]
      )
    apply HasLimit.mk {
      cone := PullbackCone.mk (W := Arrow.mk k)
        (Arrow.homMk' (u := u) (v := v) (by rw [pullback.lift_fst]))
        (Arrow.homMk' (u := r) (v := s) (by rw [pullback.lift_snd]))
        (by
          ext
          . dsimp
            rw [pcon]
          dsimp
          rw [pullback.condition])
      isLimit := PullbackCone.IsLimit.mk
        (by
          ext
          . dsimp
            rw [pcon]
          dsimp
          rw [pullback.condition])
        (λ sc ↦
          Arrow.homMk'
            (u := pullback.lift sc.fst.left sc.snd.left (Arrow.hom.congr_left sc.condition))
            (v := pullback.lift sc.fst.right sc.snd.right (Arrow.hom.congr_right sc.condition)) (by
            ext
            . have fstw: sc.fst.left ≫ f = sc.pt.hom ≫ sc.fst.right := sc.fst.w
              have : u ≫ f = k ≫ v := by rw [pullback.lift_fst]
              rw [assoc, ← this, ← assoc, pullback.lift_fst, fstw, assoc, pullback.lift_fst]
            have sndw : sc.snd.left ≫ h = sc.pt.hom ≫ sc.snd.right := sc.snd.w
            have : r ≫ h = k ≫ s := by rw [pullback.lift_snd]
            rw [assoc, ← this, ← assoc, pullback.lift_snd, sndw, assoc, pullback.lift_snd]))
        (by intro s; ext <;> dsimp <;> rw [pullback.lift_fst])
        (by intro s; ext <;> dsimp <;> rw [pullback.lift_snd])
        (by
          intro sc h hmfst hmsnd
          dsimp
          ext
          . have hfst : h.left ≫ u = sc.fst.left := Arrow.hom.congr_left hmfst
            have hsnd : h.left ≫ r = sc.snd.left := Arrow.hom.congr_left hmsnd
            dsimp
            ext
            . rw [hfst, pullback.lift_fst]
            rw [hsnd, pullback.lift_snd]
          have hfst : h.right ≫ v = sc.fst.right := Arrow.hom.congr_right hmfst
          have hsnd : h.right ≫ s = sc.snd.right := Arrow.hom.congr_right hmsnd
          dsimp
          ext
          . rw [hfst, pullback.lift_fst]
          rw [hsnd, pullback.lift_snd])
    }
  apply hasPullbacks_of_hasLimit_cospan

variable (Ω : 𝓒) [«§4.2».HasSubobjectClassifier Ω]

-- TODO: t : {0, 1/2, 1} ⟶ {0, 1} を定義したいが、{0, 1/2, 1}の定義の仕方がわからない
-- instance arrow.subobjectClassifier : «§4.2».SubobjectClassifier (Arrow.mk t) where
-- このあたりのより一般的な定義はCH.9で出てくるようなのでいったん置いておく

end «Example 5»

end «§4.4»

-- NOTE: §4.65と4.6は別ファイル

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
    (r : R ⟶ a ⨯ b) (monoRel : Mono r),
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
  -- have ⟨cOb, ⟨CHom, hmono, hPB⟩, h⟩ := Ω_axiom' ev
  have ⟨cOb, CHom, ⟨hmono, hPB⟩, h⟩ := Ω_axiom' ev
  constructor
  apply show PowerObject a from {
    𝓟a := 𝓟a
    containOb := cOb
    containHom := CHom
    monoCH := hmono
    property := by
      intro b R r hr
      let χr : a ⨯ b ⟶ Ω := χ r hr
      let fr : b ⟶ a ⇨' Ω := exp.curry χr
      have ⟨R', r', ⟨rmono, rPB⟩, runiq⟩ := Ω_axiom' <| prod.map (𝟙 a) fr ≫ ev
      let u : R' ⟶ cOb := hPB.lift (r' ≫ prod.map (𝟙 _) fr) (terminal.from _) (by simp [rPB.w])
      have hu : u ≫ terminal.from _ = terminal.from _ := hPB.lift_snd (r' ≫ prod.map (𝟙 _) fr) (terminal.from _) (by simp [rPB.w])
      rw [← hu] at rPB
      have := IsPullback.of_bot rPB (by sorry) hPB
      -- TODO: RとR'が同じであることを証明しないといけないけど出来る？
      -- TODO: frのMono条件が示せない？
      sorry
  }

end «§4.7»

namespace «§4.8»
-- Ω and comprehensions

open «§4.1» «§4.2»

variable [HasTerminal 𝓒]

def catElemMembership {a b : 𝓒} (f : a ⟶ b) (x : element b) : Prop := ∃ k : element a, k ≫ f = x

instance {a b : 𝓒} : Membership (element b) (a ⟶ b) where
  mem := catElemMembership

lemma «Exercise 1» {a b c : 𝓒} (f : a ⟶ b) (g : c ⟶ b) (h : f ⊆ₛ g) (x : element b) : x ∈ f → x ∈ g := by
  intro ⟨k, hk⟩
  have ⟨i, hi⟩ := h
  use k ≫ i
  rw [assoc, hi, hk]

variable {Ω : 𝓒} [«§4.3».ElementaryTopos Ω]

lemma «Exercise 2» {a d : 𝓒} (f : a ⟶ d) (hf : Mono f) (x : element d) : x ∈ f ↔ x ≫ χ f hf = «§4.2».true (Ω := Ω) := by
  have ⟨h, _⟩ := χ.spec f hf (Ω := Ω)
  have : terminal.from (⊤_ 𝓒) = 𝟙 (⊤_ 𝓒) := by ext
  constructor
  . intro ⟨k, hk⟩
    rw [← hk, assoc, h.w, ← assoc, terminal.comp_from, this, id_comp]
  intro he
  let k := h.lift x (terminal.from _) (by rw [he, this, id_comp])
  use k
  rw [h.lift_fst]
