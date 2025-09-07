import Topoi.Chapter4

open CategoryTheory Category Limits

set_option linter.unusedSectionVars false

noncomputable section

open «CH.4».«§4.1» «CH.4».«§4.2» «CH.4».«§4.3»

variable {𝓒 : Type*} [Category 𝓒]

namespace «CH.5»

namespace «§5.1»
-- Monics equalise

variable {Ω : 𝓒} [ElementaryTopos Ω] {a b : 𝓒} (f : a ⟶ b)

section

variable [Mono f]

lemma χ.w : f ≫ χ (.mk f) = terminal.from _ ≫ true (Ω := Ω) := by
  have ⟨h, _⟩ := χ.spec (.mk f) (Ω := Ω)
  rw [h.w]

abbrev fFork := Fork.ofι
  (f := χ (.mk f))
  (g := terminal.from _ ≫ true)
  f (by rw [χ.w f (Ω := Ω), ← assoc, terminal.comp_from])

def «Theorem 1» : IsLimit (fFork f (Ω := Ω)) := by
  have ⟨h, _⟩ := χ.spec (.mk f) (Ω := Ω)
  let _lift (c : Fork (χ (.mk f) (Ω := Ω)) (terminal.from b ≫ true)) : c.pt ⟶ a := h.lift c.ι (terminal.from c.pt) (by
    have := c.condition
    dsimp at this
    rw [this, ← assoc, terminal.comp_from])
  apply Fork.IsLimit.mk (fFork f) _lift
  . intro c
    dsimp [_lift]
    rw [h.lift_fst]
  intro c hm hmι
  rw [Fork.ι_ofι] at hmι
  dsimp [_lift]
  apply h.hom_ext
  . rw [h.lift_fst, hmι]
  simp only [terminal.comp_from]

end

theorem «Corollary» (Ω : 𝓒) [ElementaryTopos Ω] : IsIso f ↔ Epi f ∧ Mono f := by
  constructor
  . apply «CH.3».«§3.3».«lemma 1»
  intro ⟨hepi, hmono⟩
  have := «Theorem 1» f (Ω := Ω)
  have eq : f = (fFork f (Ω := Ω)).ι := rfl
  rw [eq] at *
  apply isIso_limit_cone_parallelPair_of_epi
  apply this

section

abbrev tFork : Fork (𝟙 Ω) (true' Ω) := Fork.ofι true
  (g := «CH.4».«§4.2».true' Ω)
  (by rw [comp_id, ← assoc, terminal.comp_from, «CH.3».«§3.6».terminal_id, id_comp])

#check «CH.4».«§4.2».«Exercise 1»

def «Exercise» : IsLimit (tFork (Ω := Ω)) := by
  have : χ (.mk true) = 𝟙 Ω := «CH.4».«§4.2».«Exercise 1» (𝓒 := 𝓒)
  -- let ff : Fork (𝟙 Ω) (true' Ω) := this ▸ fFork (true (Ω := Ω)) ((«§3.6.ex3» true)) (Ω := Ω)
  let tf := tFork (Ω := Ω)
  have := «CH.4».«§4.2».«Exercise 1» (Ω := Ω)
  have hp := «Theorem 1» (true (Ω := Ω)) (Ω := Ω)
  -- rw [this] at hp
  -- TODO: Forkの型が違うからできない？
  -- apply IsLimit.ofIsoLimit hp (t := tFork)
  sorry

end

end «§5.1»

namespace «§5.2»
-- Image of arrow

variable {Ω : 𝓒} [ElementaryTopos Ω]

variable {a b r : 𝓒} {p q : b ⟶ r}

abbrev fa : 𝓒 := equalizer p q
abbrev imf : equalizer p q ⟶ b := equalizer.ι p q

lemma himf : Mono (equalizer.ι p q) := by
  apply «CH.3».«§3.10».«theorem 1»

variable {f : a ⟶ b} (hf : IsPushout f f p q)

abbrev fstar : a ⟶ equalizer p q := equalizer.lift f hf.w

theorem «Exercise 3» (hf : IsPushout f f p q) : p = q → Epi f := by
  intro h
  constructor
  intro c g₁ g₂ hg
  let i := hf.desc g₁ g₂ hg
  have h₁ : p ≫ i = g₁ := by rw [hf.inl_desc]
  have h₂ : q ≫ i = g₂ := by rw [hf.inr_desc]
  rw [← h₁, ← h₂, h]

theorem «Theorem 1» {c : 𝓒} (Ω : 𝓒) [ElementaryTopos Ω] (u : a ⟶ c) (v : c ⟶ b) [Mono v] (huv : u ≫ v = f) :
  ∃! k : fa (Ω := Ω) ⟶ c, fstar hf (Ω := Ω) ≫ k = u ∧ k ≫ v = imf (Ω := Ω) := by
  have hv : Mono v := inferInstance
  have :=  «§5.1».«Theorem 1» v (Ω := Ω)
  let s := χ (.mk v) (Ω := Ω)
  let t := «CH.4».«§4.2».true' b (Ω := Ω)
  let vcone := «§5.1».fFork v (Ω := Ω)
  have : v ≫ s = v ≫ t := vcone |>.condition
  let h : r ⟶ Ω := hf.desc s t (by rw [← huv, assoc, this, ← assoc])
  have hps : p ≫ h = s := by rw [hf.inl_desc]
  have hqt : q ≫ h = t := by rw [hf.inr_desc]
  have : equalizer.ι p q ≫ s = equalizer.ι p q ≫ t :=
    calc
      equalizer.ι p q ≫ s
      _ = equalizer.ι p q ≫ p ≫ h := by rw [hps]
      _ = equalizer.ι p q ≫ q ≫ h := by rw [← assoc, equalizer.condition, assoc]
      _ = equalizer.ι p q ≫ t := by rw [hqt]
  let k : fa (Ω := Ω) ⟶ c := Fork.IsLimit.lift («§5.1».«Theorem 1» v) (equalizer.ι p q) this
  have hk : k ≫ v = equalizer.ι p q := by
    apply Fork.IsLimit.lift_ι
  use k
  constructor
  . dsimp
    constructor
    . apply cancel_mono v |>.mp
      rw [assoc, hk, equalizer.lift_ι, huv]
    rw [hk]
  -- NOTE: 教科書ではuniqueの証明が無い
  intro k' ⟨hk'₁, hk'₂⟩
  apply Fork.IsLimit.hom_ext («§5.1».«Theorem 1» v (Ω := Ω))
  dsimp
  rw [hk'₂, hk]

theorem Corollary [ElementaryTopos Ω] : Epi (fstar hf (Ω := Ω)) := by
  let ga : 𝓒 := equalizer (imf (Ω := Ω) ≫ p) (equalizer.ι p q ≫ q)
  let img : ga ⟶ equalizer p q := equalizer.ι (imf (Ω := Ω) ≫ p) (imf (Ω := Ω) ≫ q)
  have hg : IsPushout (fstar hf (Ω := Ω)) (fstar hf (Ω := Ω)) (imf (Ω := Ω) ≫ p) (imf (Ω := Ω) ≫ q) := by
    sorry
  let gstar : a ⟶ ga := equalizer.lift (fstar hf (Ω := Ω)) hg.w
  have h : gstar ≫ img = fstar hf (Ω := Ω) := by
    rw [equalizer.lift_ι]
  have : Mono img := by
    apply «CH.3».«§3.10».«theorem 1»
  -- have h₁ : img ≫ imf ⊆ₛ equalizer.ι p q := by
  --   use img
  -- have h₂ : equalizer.ι p q ⊆ₛ img ≫ imf := by
  --   sorry
  have himg : IsIso img := by
    sorry
  constructor
  intro z x y hxy
  rw [← h] at hxy
  sorry

theorem «Theorem 2» {c : 𝓒} (Ω : 𝓒) [ElementaryTopos Ω] (u : a ⟶ c) (v : c ⟶ b) [Epi u] [Mono v] (huv : u ≫ v = f):
  ∃! k : fa (Ω := Ω) ⟶ c, fstar hf (Ω := Ω) ≫ k = u ∧ k ≫ v = imf (Ω := Ω) ∧ IsIso k := by
  have ⟨k, ⟨hk₁, hk₂⟩, huniq⟩ := «Theorem 1» hf Ω u v huv
  have hv : Mono v := inferInstance
  have hu : Epi u := inferInstance
  use k
  constructor
  . constructor
    apply hk₁
    constructor
    apply hk₂
    have kmono : Mono k := by
      apply «CH.3».«§3.1».Excercises.«(2)» 𝓒 k v
      rw [hk₂]
      apply himf (Ω := Ω)
    have kepi : Epi k := by
      apply «CH.3».«§3.1».Excercises.«(2)'» 𝓒 (fstar (Ω := Ω) hf) k
      rw [hk₁]
      apply hu
    apply «§5.1».Corollary k Ω |>.mpr ⟨kepi, kmono⟩
  -- NOTE: 教科書ではuniqueの証明が無い
  intro k' ⟨hk'₁, hk'₂, hkuniq'⟩
  apply Fork.IsLimit.hom_ext («§5.1».«Theorem 1» v (Ω := Ω))
  dsimp
  rw [hk'₂, hk₂]

theorem «Exercise 4» [ElementaryTopos Ω] : Epi f ↔ ∃ g : fa (Ω := Ω) ≅ b, (fstar (Ω := Ω) hf) ≫ g.hom = f := by
  constructor
  . intro hepi
    have ⟨k, ⟨hk₁, hk₂, hkiso⟩, hkuniq⟩ := «Theorem 2» hf Ω f (𝟙 b) (by rw [comp_id])
    rw [comp_id] at hk₂
    rw [hk₂] at hk₁ hkiso
    use asIso <| imf (Ω := Ω)
    rw [asIso_hom, equalizer.lift_ι]
  intro ⟨g, hg⟩
  sorry

variable (f)
lemma eqPushout : ∃ (r : 𝓒) (p q : b ⟶ r), IsPushout f f p q := by
  have : HasPushout f f := by
    infer_instance
  let r := pushout f f
  let p := pushout.inl f f
  let q := pushout.inr f f
  use r, p, q
  apply IsPushout.mk
  . constructor
    apply pushoutIsPushout
  constructor
  apply pushout.condition

lemma fFactor [ElementaryTopos Ω] : ∃ (fa : 𝓒) (fstar' : a ⟶ fa) (imf' : fa ⟶ b),
    fstar' ≫ imf' = f ∧ Epi fstar' ∧ Mono imf' ∧
    ∀ {c : 𝓒} (u : a ⟶ c) (v : c ⟶ b) [Epi u] [Mono v] (huv : u ≫ v = f),
    ∃! k : fa ⟶ c, fstar' ≫ k = u ∧ k ≫ v = imf' ∧ IsIso k
    := by
  have ⟨r, p, q, h⟩ := eqPushout f
  let fa := equalizer p q
  let fstar' := equalizer.lift f h.w
  let imf' := equalizer.ι p q
  use fa, fstar', imf'
  constructor
  . rw [equalizer.lift_ι]
  constructor
  . apply Corollary h (Ω := Ω)
  constructor
  . apply himf (Ω := Ω)
  have hfstar : fstar' = fstar (Ω := Ω) h := by dsimp [fstar]
  have himf : imf' = imf (Ω := Ω) := by dsimp [imf]
  rw [hfstar, himf]
  intro c
  apply «Theorem 2» h Ω

variable (Ω)
abbrev fa' : 𝓒 := fFactor f (Ω := Ω) |>.choose
notation f ":'" Ω "(" a ")" => fa' Ω f (a := a)
abbrev fstar' : a ⟶ f:'Ω(a) := fFactor f (Ω := Ω) |>.choose_spec |>.choose
abbrev im : f:'Ω(a) ⟶ b := fFactor f (Ω := Ω) |>.choose_spec |>.choose_spec |>.choose
notation f ":'" Ω "*'" => fstar' Ω f

def epiMonoFactor : (f:'Ω*') ≫ (im Ω f) = f
  := fFactor f (Ω := Ω) |>.choose_spec |>.choose_spec |>.choose_spec |>.1
def epiFstar : Epi (f:'Ω*')
  := fFactor f (Ω := Ω) |>.choose_spec |>.choose_spec |>.choose_spec |>.2.1
def monoImage : Mono (im Ω f)
  := fFactor f (Ω := Ω) |>.choose_spec |>.choose_spec |>.choose_spec |>.2.2.1
def epiMonoUniversal : ∀ {c : 𝓒} (u : a ⟶ c) (v : c ⟶ b) [Epi u] [Mono v] (huv : u ≫ v = f),
    ∃! k : f:'Ω(a) ⟶ c, f:'Ω*' ≫ k = u ∧ k ≫ v = im Ω f ∧ IsIso k
  := fFactor f (Ω := Ω) |>.choose_spec |>.choose_spec |>.choose_spec |>.2.2.2

end «§5.2»

namespace «§5.3»
-- Fundamental facts

variable [HasPullbacks 𝓒]

axiom «Fact 1» {a b c d : 𝓒} {f₁ : a ⟶ b} {f₂ : c ⟶ d} {f : b ⟶ d} {g : a ⟶ c}
  (h : IsPullback f₁ g f f₂) [Epi f] : Epi g

variable [HasBinaryCoproducts 𝓒]

axiom «Fact 2» {a b d e a' b' : 𝓒}
  {f : a ⟶ d} {g : a ⟶ b} {h : b ⟶ e} {k : d ⟶ e}
  {f' : a' ⟶ d} {g' : a' ⟶ b'} {h' : b' ⟶ e}
  (h₁ : IsPullback f g k h) (h₂ : IsPullback f' g' k h') :
  IsPullback (coprod.desc f f') (coprod.map g g') k (coprod.desc h h')

end «§5.3»

namespace «§5.4»
-- Extensionality and bivalence

open «CH.4».«§4.1»

section

variable [HasTerminal 𝓒] [HasInitial 𝓒]

variable (a : 𝓒)

-- NOTE: ≅は構造体のため否定が取れないため、IsIsoの否定の形にした
abbrev nonZero := ¬ (IsIso (initial.to a))
abbrev nonEmpty := Nonempty (element a)

end

def «Extensionality Principle For Arrows» {a b : 𝓒} (f g : a ⟶ b) : Prop
  := ∀ (h : f ≠ g), ∃ x : element a, x ≫ f ≠ x ≫ g

variable (𝓒)
abbrev degenerate := ∀ a b : 𝓒, a ≅ b
abbrev nonDegenerate [HasInitial 𝓒] := ¬ IsIso (initial.to (⊤_ 𝓒))
variable {Ω : 𝓒}

-- TODO: 本当はnon-degenerateで外延性を持つトポスだが、ElementaryToposの定義とうまく併せられなかった
class WellPointed extends HasInitial 𝓒 where
  nd : ¬ IsIso (initial.to (⊤_ 𝓒))
  epfa : ∀ {a b : 𝓒} (f g : a ⟶ b), «Extensionality Principle For Arrows» f g

instance WellPointed.nd' [WellPointed 𝓒] : nonDegenerate 𝓒 := WellPointed.nd (𝓒 := 𝓒)
instance WellPointed.epfa' [WellPointed 𝓒]
    : ∀ {a b : 𝓒} (f g : a ⟶ b), «Extensionality Principle For Arrows» f g := WellPointed.epfa (𝓒 := 𝓒)

variable {𝓒}

lemma WellPointed.hom_ext {a b : 𝓒} [ElementaryTopos Ω] [WellPointed 𝓒] {f g : a ⟶ b}
  (h : ∀ x : element a, x ≫ f = x ≫ g) : f = g := by
  by_contra hn
  have ⟨x, hx⟩ := WellPointed.epfa' 𝓒 f g hn
  apply hx
  apply h x

instance hMonoIni [HasInitial 𝓒] {a : 𝓒} : Mono (initial.to a) := «CH.3».«§3.16».«Theorem 1».«(4)» _

theorem «Theorem 1» [WellPointed 𝓒] [ElementaryTopos Ω] : ∀ a : 𝓒, nonZero a → nonEmpty a := by
  intro a ha
  let za : subset a := .mk <| initial.to a
  let oa : subset a := .mk <| 𝟙 a
  have : ¬ za ≈ oa := by
    intro ⟨⟨f₁, hf₁⟩, ⟨f₂, hf₂⟩⟩
    dsimp [oa, za] at *
    rw [comp_id] at hf₁
    apply ha
    constructor
    use f₂
    constructor
    . rw [initial.to_comp]
      ext
    apply hf₂
  have : χ za ≠ χ oa := «CH.4».«§4.2».Theorem za oa (Ω := Ω) |>.not.mp this
  have ⟨x, hx⟩ := WellPointed.epfa' _ (χ za) (χ oa) this
  constructor
  use x

abbrev false' [ElementaryTopos Ω] : ⊤_ 𝓒 ⟶ Ω := χ <| .mk <| initial.to _

abbrev false [ElementaryTopos Ω] (a : 𝓒) : a ⟶ Ω := terminal.from a ≫ false'

lemma init_top_eq_terminal_bot [HasTerminal 𝓒] [HasInitial 𝓒] : terminal.from (⊥_ 𝓒) = initial.to (⊤_ 𝓒) := by ext

-- IsPullback (initial.to a) (terminal.from (⊥_ 𝓒)) (false a) true
theorem «Exercise 3» [ElementaryTopos Ω] (a : 𝓒) : χ (.mk <| initial.to _) = false a (Ω := Ω) := by
  have ⟨_, huniq⟩ := χ.spec (.mk <| initial.to a) (Ω := Ω)
  symm
  apply huniq <| false a
  dsimp [false]
  have : terminal.from (⊥_ 𝓒) = 𝟙 _ ≫ initial.to _ := by
    rw [id_comp]
    ext
  rw [this]
  apply IsPullback.paste_vert (h₂₁ := initial.to _)
  . constructor
    . constructor
      apply PullbackCone.IsLimit.mk (by rw [id_comp, initial.to_comp]) (λ s ↦ s.snd)
      . intro s
        have hi : initial.to (⊤_ 𝓒) = initial.to a ≫ terminal.from a := by
          rw [initial.to_comp]
        have : Mono (terminal.from a) := by
          constructor
          intro x f g hfg
          -- TODO: これは証明できなさそう
          sorry
        apply cancel_mono (terminal.from a) |>.mp
        rw [s.condition, assoc, ← hi]
      . intro s
        rw [comp_id]
      intro s m hmfst hmsnd
      rw [comp_id] at hmsnd
      apply hmsnd
    constructor
    rw [id_comp, initial.to_comp]
  have ⟨hPB, _⟩ := χ.spec (.mk <| initial.to (⊤_ 𝓒)) (Ω := Ω)
  rw [init_top_eq_terminal_bot] at hPB
  apply hPB

theorem «Exercise 4» [ElementaryTopos Ω] [WellPointed 𝓒] : true (Ω := Ω) ≠ false' := by
  intro h
  apply WellPointed.nd' 𝓒
  constructor
  dsimp [false'] at h
  rw [← «CH.4».«§4.2».«Exercise 2'»] at h
  have ⟨⟨f, hf⟩, ⟨finv, hfinv⟩⟩ := «CH.4».«§4.2».Theorem (.mk <| 𝟙 _) (.mk <| initial.to _) |>.mpr h
  use f
  constructor
  . rw [initial.to_comp]
    ext
  rw [hf]

variable (𝓒)
abbrev bivalent [ElementaryTopos Ω] (nd : nonDegenerate 𝓒) : Prop
  := ∀ f : element Ω, f = true (Ω := Ω) ∨ f = false'
variable {𝓒}

theorem «Theorem 2» [ElementaryTopos Ω] [WellPointed 𝓒]: bivalent 𝓒 (WellPointed.nd' 𝓒) (Ω := Ω) := by
  intro f
  let g := rf.subset_f f
  let a := g.dom
  have hPB := rf.f.PB f
  let χf := χ g (Ω := Ω)
  have ⟨hfPB, hfuniq⟩ := χ.spec g (Ω := Ω)
  by_cases h : IsIso (initial.to a)
  . have ia : IsInitial a := IsInitial.ofIso initialIsInitial <| asIso (initial.to a)
    right
    apply hfuniq f hPB |>.trans
    dsimp [false']
    -- TODO: このあたりの書き方をリファクタリングする
    apply «CH.4».«§4.2».Theorem g (.mk <| initial.to _) |>.mp
    constructor
    . use ia.to _
      rw [ia.to_comp, ia.hom_ext g.ar (ia.to _)]
    use initial.to _
    rw [initial.to_comp]
  have x : element a := Classical.choice <| «Theorem 1» (Ω := Ω) a h
  have hgepi : Epi g.ar := by
    constructor
    intro b h k hg
    have hg : x ≫ g.ar ≫ h = x ≫ g.ar ≫ k := by congr
    have : x ≫ g.ar = 𝟙 _ := by ext
    rw [← assoc, ← assoc, this, id_comp, id_comp] at hg
    apply hg
  have hgmono : Mono g.ar := g.mono
  have := «§5.1».Corollary g.ar Ω |>.mpr ⟨hgepi, hgmono⟩
  let g' : a ≅ ⊤_ 𝓒 := asIso g.ar
  have ta : IsTerminal a := IsTerminal.ofIso terminalIsTerminal g'.symm
  left
  apply hfuniq f hPB |>.trans
  rw [← «CH.4».«§4.2».«Exercise 2'»]
  apply «CH.4».«§4.2».Theorem g (.mk <| 𝟙 _) |>.mp
  constructor
  . use g'.hom
    rw [comp_id, asIso_hom]
  use g'.inv
  rw [asIso_inv, IsIso.inv_hom_id]

variable (𝓒) (Ω)
abbrev ClassicalTopos [ElementaryTopos Ω] : Prop := IsIso (coprod.desc (true (Ω := Ω)) false')
variable {𝓒} {Ω}

section

variable {a b c : 𝓒} (f : a ⟶ b) (g : c ⟶ b)

abbrev disjointArr [HasInitial 𝓒] : Prop := IsPullback (initial.to c) (initial.to a) g f

variable {f} {g}
theorem «Lemma» [HasInitial 𝓒] [HasBinaryCoproducts 𝓒] [Mono f] [Mono g] (hd : disjointArr f g) : Mono (coprod.desc f g) := by
  have hf : Mono f := inferInstance
  have hg : Mono g := inferInstance
  have hPBg : IsPullback (𝟙 c) coprod.inr g (coprod.desc f g) := by
    have hgPB := «CH.3».«§3.13».«Example 9» 𝓒 g |>.mp hg
    have hPB := «§5.3».«Fact 2» hd hgPB
    -- ただの同型だけでなく具体的な射の情報も必要だったので明示的に構成した
    -- have hzo : c ≅ (⊥_ 𝓒) ⨿ c := «CH.3».«§3.8».Excercises.«4'» ≪≫ coprod.braiding _ _
    let hzo : c ≅ (⊥_ 𝓒) ⨿ c := «CH.3».«§3.8».Excercises.«4'''» 𝓒
    apply IsPullback.of_iso hPB hzo.symm (.refl _) (.refl _) (.refl _)
      (fst' := 𝟙 _) (snd' := coprod.inr) (f' := g) (g' := coprod.desc f g)
    . dsimp
      have : coprod.desc (initial.to _) (𝟙 _) = hzo.inv := rfl
      rw [this]
    . dsimp
      rw [comp_id]
      ext
      have : coprod.inr = hzo.hom := rfl
      rw [coprod.inr_map, this, ← assoc, hzo.hom_inv_id]
    . simp
    simp

  -- 共通化したかったが、同じようにやるとpullback squareの左下がa ⨿ cとc ⨿ aになってしまう
  -- そこを併せるために再度IsPullback.of_isoが必要になるのでそのまま同じことをやることにする
  have hPBf : IsPullback (𝟙 a) coprod.inl f (coprod.desc f g) := by
    have hfPB := «CH.3».«§3.13».«Example 9» 𝓒 f |>.mp hf
    have hPB := «§5.3».«Fact 2» hfPB hd.flip
    let hzo : a ≅ a ⨿ (⊥_ 𝓒) := «CH.3».«§3.8».Excercises.«4''» 𝓒
    apply IsPullback.of_iso hPB hzo.symm (.refl _) (.refl _) (.refl _)
      (fst' := 𝟙 _) (snd' := coprod.inl) (f' := f) (g' := coprod.desc f g)
    . dsimp
      have : coprod.desc (𝟙 _) (initial.to _) = hzo.inv := rfl
      rw [this]
    . dsimp
      rw [comp_id]
      ext
      have : coprod.inl = hzo.hom := rfl
      rw [coprod.inl_map, this, ← assoc, hzo.hom_inv_id]
    . simp
    simp
  have := «§5.3».«Fact 2» hPBf.flip hPBg.flip
  rw [coprod.map_id_id, coprod.desc_inl_inr] at this
  apply «CH.3».«§3.13».«Example 9» _ _ |>.mpr this

end

theorem «Theorem 3» [ElementaryTopos Ω] : Mono (coprod.desc (true (Ω := Ω)) false') := by
  apply «Lemma»
  have ⟨hPB, _⟩ := χ.spec (.mk <| initial.to (⊤_ 𝓒)) (Ω := Ω)
  rw [init_top_eq_terminal_bot] at hPB
  apply hPB

theorem «Theorem 4» [ElementaryTopos Ω] [WellPointed 𝓒] : ClassicalTopos 𝓒 Ω := by
  apply «§5.1».Corollary (coprod.desc (true (Ω := Ω)) false') Ω |>.mpr
  constructor
  . constructor
    intro a f g hfg
    have htrue : true (Ω := Ω) ≫ f = true ≫ g := by
      calc
        true ≫ f
        _ = coprod.inl ≫ coprod.desc true false' ≫ f := by rw [← assoc, coprod.inl_desc]
        _ = coprod.inl ≫ coprod.desc true false' ≫ g := by rw [hfg]
        _ = true ≫ g := by rw [← assoc, coprod.inl_desc]
    have hfalse : false' ≫ f = false' ≫ g := by
      calc
        false' ≫ f
        _ = coprod.inr ≫ coprod.desc true false' ≫ f := by rw [← assoc, coprod.inr_desc]
        _ = coprod.inr ≫ coprod.desc true false' ≫ g := by rw [hfg]
        _ = false' ≫ g := by rw [← assoc, coprod.inr_desc]
    have : ∀ x : element Ω, x = true (Ω := Ω) ∨ x = false' := «Theorem 2» (Ω := Ω)
    by_contra nh
    have ⟨x, hx⟩ := WellPointed.epfa' 𝓒 f g nh
    apply hx
    match this x with
    | .inl h =>
      rw [h, htrue]
    | .inr h =>
      rw [h, hfalse]
  apply «Theorem 3»

theorem «Theorem 5» [ElementaryTopos Ω] : WellPointed 𝓒 ↔ ClassicalTopos 𝓒 Ω ∧ ∀ a : 𝓒, nonZero a → nonEmpty a := by
  constructor
  . intro h
    constructor
    . apply «Theorem 4»
    apply «Theorem 1» (Ω := Ω)
  -- NOTE: if条件は§7.6で証明される
  sorry

-- TODO: この後のモノイドの内容はM-Setの圏が定義できていないのでスキップ

end «§5.4»

namespace «§5.5»
-- Monics and epics by elements

open «CH.4».«§4.1» «§5.4»

variable {a b : 𝓒} (f : a ⟶ b)

abbrev surjective : Prop := ∀ y : element b, ∃ x : element a, x ≫ f = y
abbrev injective : Prop := ∀ x y : element a, x ≫ f = y ≫ f → x = y

namespace «Theorem 1»

variable {Ω : 𝓒}

theorem «(i)» [ElementaryTopos Ω] [WellPointed 𝓒] : surjective f ↔ Epi f := by
  constructor
  . intro hsur
    constructor
    intro c g h hg
    by_contra hne
    have ⟨y, hy⟩ := WellPointed.epfa' 𝓒 g h hne
    have ⟨x, hx⟩ := hsur y
    have : y ≫ g = y ≫ h := by
      calc
        y ≫ g
        _ = x ≫ f ≫ g := by rw [← assoc, hx]
        _ = x ≫ f ≫ h := by rw [hg]
        _ = y ≫ h := by rw [← assoc, hx]
    contradiction
  intro hepi y
  let c : 𝓒 := pullback y f
  let p : c ⟶ ⊤_ 𝓒 := pullback.fst y f
  let q : c ⟶ a := pullback.snd y f
  have hpEpi : Epi p := «§5.3».«Fact 1» (IsPullback.of_hasPullback y f).flip
  by_cases h : IsIso (initial.to c)
  . have hI : IsInitial c := by
      apply IsInitial.ofIso initialIsInitial
      apply asIso (initial.to c)
    have hpMono : Mono p := by
      apply «CH.3».«§3.16».«Theorem 1».IsInitial.«(4)» hI
    have hpIso : IsIso p := by
      apply «§5.1».Corollary p Ω |>.mpr ⟨hpEpi, hpMono⟩
    have : ⊥_ 𝓒 ≅ ⊤_ 𝓒 := by
      apply initialIsoIsInitial hI |>.trans
      apply asIso p
    have : degenerate 𝓒 := «CH.3».«§3.16».«Theorem 1».«(3)» this
    let hzo := this (⊤_ 𝓒) c
    let z : ⊤_ 𝓒 ⟶ c := hzo.hom
    have : pullback.fst y f = hzo.inv := by ext
    use z ≫ q
    rw [assoc, ← pullback.condition, ← assoc, this, hzo.hom_inv_id, id_comp]
  -- 教科書にはこの証明の記載なし
  have : nonEmpty c := «Theorem 1» c h (Ω := Ω)
  let z : element c := Classical.choice this
  have : z ≫ p = 𝟙 _ := by ext
  use z ≫ q
  rw [assoc, ← pullback.condition, ← assoc, this, id_comp]

theorem «(ii)» [ElementaryTopos Ω] [WellPointed 𝓒] : injective f ↔ Mono f := by
  constructor
  . intro hinj
    constructor
    intro c g h hg
    apply WellPointed.hom_ext (Ω := Ω)
    intro x
    apply hinj
    simp only [assoc, hg]
  intro ⟨hmono⟩ x y hxy
  apply hmono
  apply hxy

-- TODO: この後のモノイドの内容はM-Setの圏が定義できていないのでスキップ
end «Theorem 1»

end «§5.5»

end «CH.5»
