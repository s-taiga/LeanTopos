import Topoi.Chapter6

open CategoryTheory Category Limits

noncomputable section

open «CH.4».«§4.2» «CH.4».«§4.3» «CH.4».«§4.1»

variable {𝓒 : Type*} [Category 𝓒]

namespace «CH.7»
-- Algebra of subobjects

namespace «§7.1»
-- Complement, intersection, union

section
variable {a b c : 𝓒} {f₁ f₂ : c ⟶ a} {g₁ g₂ : c ⟶ b}
lemma prod.lift_eq_fst (h : prod.lift f₁ g₁ = prod.lift f₂ g₂) : f₁ = f₂ := by
  have := congrArg (· ≫ prod.fst) h
  simp [prod.lift_fst] at this
  apply this

lemma prod.lift_eq_snd (h : prod.lift f₁ g₁ = prod.lift f₂ g₂) : g₁ = g₂ := by
  have := congrArg (· ≫ prod.snd) h
  simp [prod.lift_snd] at this
  apply this
end

variable {d : 𝓒} (Ω : 𝓒) [ElementaryTopos Ω]

namespace complement

open «CH.6».«§6.6»

abbrev ob (f : subset d) : 𝓒
  := rf.a <| χ f (Ω := Ω) ≫ negT

abbrev ar (f : subset d) : ob f (Ω := Ω) ⟶ d
  := rf.f <| χ f (Ω := Ω) ≫ negT

instance : Neg (subset d) where
  neg f := .mk <| ar f (Ω := Ω)

lemma eq (f : subset d) : χ (.mk <| ar Ω f) = χ f (Ω := Ω) ≫ negT := by
  rw [← rf.subset_f.eq]

notation:80 "∸o(" Ω ") " f => ob Ω f
notation:80 "∸a(" Ω ") " f => ar Ω f

lemma ext {f f' : subset d} (h : f ≈ f')
    : subset.mk (∸a(Ω) f) ≈ .mk (∸a(Ω) f') := by
  apply «CH.4».«§4.2».Theorem _ _ (Ω := Ω) |>.mpr
  have h₁ : χ f = χ f' := «CH.4».«§4.2».Theorem _ _ (Ω := Ω) |>.mp h
  rw [← rf.subset_f.eq, ← rf.subset_f.eq, h₁]

end complement

namespace intersection

abbrev ob (f g : subset d) : 𝓒 := rf.a <| χ f ∩(Ω) χ g
abbrev ar (f g : subset d) : ob f g (Ω := Ω) ⟶ d := rf.f <| χ f ∩(Ω) χ g

lemma eq (f g : subset d) : χ (.mk <| ar Ω f g) = χ f ∩(Ω) χ g := by
  rw [← rf.subset_f.eq]

notation:80 f " ⋒o(" Ω ") " g => ob Ω f g
notation:80 f " ⋒a(" Ω ") " g => ar Ω f g

end intersection

namespace union

variable [ElementaryTopos Ω]

abbrev ob (f g : subset d) : 𝓒 := rf.a <| χ f ∪(Ω) χ g
abbrev ar (f g : subset d) : ob f g (Ω := Ω) ⟶ d := rf.f <| χ f ∪(Ω) χ g

lemma eq (f g : subset d) : χ (.mk <| ar Ω f g) = χ f ∪(Ω) χ g := by
  rw [← rf.subset_f.eq]

notation:80 f " ⋓o(" Ω ") " g => ob Ω f g
notation:80 f " ⋓a(" Ω ") " g => ar Ω f g

lemma ext {f g f' g' : subset d} (h₁ : f ≈ f') (h₂ : g ≈ g')
    : subset.mk (f ⋓a(Ω) g) ≈ .mk (f' ⋓a(Ω) g') := by
  apply «CH.4».«§4.2».Theorem _ _ (Ω := Ω) |>.mpr
  have h₁ : χ f = χ f' := «CH.4».«§4.2».Theorem _ _ (Ω := Ω) |>.mp h₁
  have h₂ : χ g = χ g' := «CH.4».«§4.2».Theorem _ _ (Ω := Ω) |>.mp h₂
  rw [← rf.subset_f.eq, ← rf.subset_f.eq, h₁, h₂]

lemma sub_out_eq_subset (f g : subset d) : subset.mk (f ⋓a(Ω) g) ≈ .mk ((⟦f⟧ : Sub d).out ⋓a(Ω) (⟦g⟧ : Sub d).out) := by
  dsimp [ar]
  apply «CH.4».«§4.2».Theorem _ _ (Ω := Ω) |>.mpr
  rw [← rf.subset_f.eq, ← rf.subset_f.eq, χ.sub_out_eq_subset, χ.sub_out_eq_subset]

end union


open «CH.6».«§6.7» in
theorem «Theorem 2» {a b c d : 𝓒}
  (f : a ⟶ d) [Mono f] (g : b ⟶ d) [Mono g]
  (f' : c ⟶ b) [Mono f'] (g' : c ⟶ a) [Mono g']
  (hPB : IsPullback f' g' g f)
  : χ (.mk <| f' ≫ g) (Ω := Ω) = χ (.mk <| .mk f ⋒a(Ω) .mk g) := by
  set α := f' ≫ g with hα
  set χf := χ (.mk f) (Ω := Ω)
  set χg := χ (.mk g) (Ω := Ω)
  set trtr := (prod.lift (TRUE Ω) (TRUE Ω)) with htrtr
  -- NOTE: 教科書に証明無し
  have hPB1 : IsPullback α (terminal.from c) (prod.lift χf χg) trtr := by
    have ⟨hχf, _⟩ := χ.spec (.mk f) (Ω := Ω)
    have ⟨hχg, _⟩ := χ.spec (.mk g) (Ω := Ω)
    have h1 : α ≫ χf = (terminal.from c) ≫ TRUE Ω := by
      rw [hα, hPB.w, assoc, hχf.w, ← assoc, terminal.comp_from]
    have h2 : α ≫ χg = (terminal.from c) ≫ TRUE Ω := by
      rw [hα, assoc, hχg.w, ← assoc, terminal.comp_from]
    have h' : α ≫ prod.lift χf χg = (terminal.from c) ≫ trtr := by
      rw [prod.comp_lift, h1, h2, ← prod.comp_lift]
    let cone : PullbackCone (prod.lift χf χg) trtr := .mk α (terminal.from c) h'
    apply IsPullback.of_isLimit (c := cone)
    apply PullbackCone.IsLimit.mk h' (λ s ↦
      have : prod.lift (s.fst ≫ χf) (s.fst ≫ χg) = prod.lift (s.snd ≫ TRUE Ω) (s.snd ≫ TRUE Ω) := by
        simp [← prod.comp_lift]
        apply s.condition
      have h : s.snd = terminal.from _ := by ext
      let f₁ := hχf.lift s.fst (terminal.from _) (by rw [prod.lift_eq_fst this, h])
      let f₂ := hχg.lift s.fst (terminal.from _) (by rw [prod.lift_eq_snd this, h])
      hPB.lift f₂ f₁ (by rw [hχg.lift_fst, hχf.lift_fst]))
    . intro s
      rw [← assoc, hPB.lift_fst, hχg.lift_fst]
    . intro s
      dsimp
      rw [terminal.comp_from]
      ext
    intro s m hmfst hmsnd
    dsimp
    apply hPB.hom_ext
    . rw [hPB.lift_fst]
      apply hχg.hom_ext
      . rw [hχg.lift_fst, assoc, hmfst]
      ext
    rw [hPB.lift_snd]
    apply hχf.hom_ext
    . rw [hχf.lift_fst, assoc, ← hPB.w, hmfst]
    ext
  have hPB2 : IsPullback trtr (𝟙 _) «CH.6».«§6.6».conT (TRUE Ω) := by
    rw [← «CH.3».«§3.6».terminal_id]
    apply χ.spec (.mk trtr) |>.1
  have hPB3 := hPB1.paste_vert hPB2
  rw [comp_id] at hPB3
  have ⟨_, huniq⟩ := χ.spec (.mk α) (Ω := Ω)
  have := huniq (prod.lift χf χg ≫ «CH.6».«§6.6».conT) hPB3 |>.symm
  rw [this, ← rf.subset_f.eq]

-- Theorem 2の後半内容
lemma subs_equiv_pullback {a b d c c' : 𝓒}
  {f : a ⟶ d} {g : b ⟶ d} {f' : c ⟶ b} {g' : c ⟶ a}
  [Mono f] [Mono g] [Mono f'] [Mono g']
  {α : c' ⟶ d} [Mono α]
  (h : (subset.mk <| f' ≫ g) ≈ (.mk α)) (hPB : IsPullback f' g' g f)
  : ∃ (p : c' ⟶ b) (q : c' ⟶ a), α = p ≫ g ∧ Mono p ∧ Mono q ∧ IsPullback p q g f := by
  -- TODO: α = p ≫ g を戻り値に加える、hjを使えばよい
  have ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := h
  dsimp [subset.dom, subset.ar] at i j hi hj
  let p : c' ⟶ b := j ≫ f'
  let q : c' ⟶ a := j ≫ g'
  have ⟨iiso, jiso⟩ := «CH.4».«§4.1».equiv_iso hi hj
  use p, q
  constructor
  . rw [assoc, hj]
  constructor
  . apply mono_comp
  constructor
  . apply mono_comp
  have w : p ≫ g = q ≫ f := by
    dsimp [p, q]
    simp only [assoc]
    rw [hPB.w]
  let cone : PullbackCone g f := .mk p q w
  apply IsPullback.of_isLimit (c := cone)
  apply PullbackCone.IsLimit.mk w (λ s ↦ hPB.lift s.fst s.snd s.condition ≫ i)
  . intro s
    apply cancel_mono g |>.mp
    rw [assoc, assoc, assoc, hj, hi, ← assoc, hPB.lift_fst]
  . intro s
    apply cancel_mono f |>.mp
    rw [assoc, assoc, assoc, ← hPB.w, hj, hi, ← assoc, hPB.lift_fst, s.condition]
  intro s m hmfst hmsnd
  dsimp [p, q] at hmfst hmsnd
  apply cancel_mono α |>.mp
  rw [assoc, hi, ← assoc, hPB.lift_fst, ← hmfst, assoc, assoc, hj]

lemma getPullbackCone {a b d : 𝓒} (Ω : 𝓒) [ElementaryTopos Ω] {f : a ⟶ d} (hf : Mono f) {g : b ⟶ d} (hg : Mono g)
  : IsPullback (pullback.snd f g) (pullback.fst f g) g f ∧ Mono (pullback.snd f g) ∧ Mono (pullback.fst f g) := by
  let c := pullback f g
  let f' := pullback.snd f g
  let g' := pullback.fst f g
  have hPB : IsPullback f' g' g f := by
    apply IsPullback.flip
    let c : PullbackCone f g := .mk g' f' pullback.condition
    apply IsPullback.of_isLimit (c := c)
    apply pullbackIsPullback f g
  constructor
  . exact hPB
  constructor
  apply «CH.3».«§3.13».Exercise _ _ _ _ _ hPB.flip hf
  apply «CH.3».«§3.13».Exercise _ _ _ _ _ hPB hg

lemma «Theorem 2'» {a b d : 𝓒} (Ω : 𝓒) [ElementaryTopos Ω] (f : a ⟶ d) (g : b ⟶ d) [Mono f] [Mono g]
  : ∃ (p : (.mk f ⋒o(Ω) .mk g) ⟶ b) (q : (.mk f ⋒o(Ω) .mk g) ⟶ a),
  (.mk f ⋒a(Ω) .mk g) = p ≫ g ∧ Mono p ∧ Mono q ∧ IsPullback p q g f := by
  -- TODO: .mk f ⋒a(Ω) .mk g = p ≫ gを戻り値に加える、«§7.1».subs_equiv_pullbackの戻り値をそのまま使う
  let f' := pullback.snd f g
  let g' := pullback.fst f g
  have ⟨hPB, hf', hg'⟩ := getPullbackCone Ω ‹Mono f› ‹Mono g›
  have := «§7.1».«Theorem 2» f g f' g' hPB (Ω := Ω)
  have := «CH.4».«§4.2».Theorem _ _ |>.mpr this
  apply «§7.1».subs_equiv_pullback this hPB

variable [ElementaryTopos Ω]

-- NOTE: 教科書では任意の圏としていたが、epi-mono分解ができるのはトポスの特徴なのでトポスを仮定
open «CH.5».«§5.2» in
theorem «Lemma» {a b c d : 𝓒}
    {f : a ⟶ b} {g : c ⟶ d} {u : a ⟶ c} {v : b ⟶ d}
    (hPB : IsPullback f u v g)
    : ∃ h : fa' Ω f ⟶ fa' Ω g, IsPullback (im Ω f) h v (im Ω g) := by
  let e := pullback v (im Ω g)
  set i := pullback.fst v (im Ω g) with hi
  set h' := pullback.snd v (im Ω g) with hh'
  let hPBe : IsPullback i h' v (im Ω g) := by
    have := pullbackIsPullback v (im Ω g)
    rw [hi, hh']
    apply IsPullback.of_isLimit this
  have hiMono := «CH.3».«§3.13».Exercise 𝓒 _ _ _ _ hPBe.flip <| monoImage _ g
  let f' : a ⟶ e := pullback.lift f (u ≫ fstar' Ω g) (by rw [assoc, epiMonoFactor, hPB.w])
  have hf'fst : f' ≫ i = f := pullback.lift_fst f (u ≫ fstar' Ω g) (by rw [assoc, epiMonoFactor, hPB.w])
  have hf'snd := pullback.lift_snd f (u ≫ fstar' Ω g) (by rw [assoc, epiMonoFactor, hPB.w])
  have hPB' : IsPullback (f' ≫ i) u v (fstar' Ω g ≫ im Ω g) := by
    rw [epiMonoFactor, hf'fst]
    apply hPB
  have hPBleft := hPB'.of_right hf'snd hPBe
  have : Epi (g:'Ω*') := epiFstar Ω g
  have hf'Epi : Epi f' := «CH.5».«§5.3».«Fact 1» hPBleft.flip
  have ⟨k, hkw, hkuniq⟩ := epiMonoUniversal Ω f f' i hf'fst
  dsimp at hkw
  have ⟨hkstar, hkim, hkiso⟩ := hkw

  use k ≫ h'
  have w : im Ω f ≫ v = (k ≫ h') ≫ im Ω g := by
    rw [assoc, ← hPBe.w, ← assoc, hkim]
  let cone : PullbackCone v (im Ω g) := .mk (im Ω f) (k ≫ h') w
  apply IsPullback.of_isLimit (c := cone)
  apply PullbackCone.IsLimit.mk w (λ s ↦ hPBe.lift s.fst s.snd s.condition ≫ inv k)
  . intro s
    rw [← hkim, assoc, ← assoc (inv k), hkiso.inv_hom_id, id_comp, hPBe.lift_fst]
  . intro s
    rw [assoc, ← assoc (inv k), hkiso.inv_hom_id, id_comp, hPBe.lift_snd]
  intro s m hmfst hmsnd
  rw [← hkim] at hmfst
  have : m ≫ k = hPBe.lift s.fst s.snd s.condition := by
    apply hPBe.hom_ext
    . rw [assoc, hmfst, hPBe.lift_fst]
    rw [assoc, hmsnd, hPBe.lift_snd]
  rw [← this, assoc, hkiso.hom_inv_id, comp_id]

open «CH.5».«§5.2» «CH.6».«§6.7» in
theorem «Theorem 3» {a b d : 𝓒} (f : a ⟶ d) (hf : Mono f) (g : b ⟶ d) (hg : Mono g)
  : χ ⟨_, im Ω (coprod.desc f g), monoImage Ω _⟩ (Ω := Ω) = χ (.mk <| (.mk f ⋓a(Ω) .mk g)) := by
  have ⟨hχf, _⟩ := χ.spec (.mk f) (Ω := Ω)
  have ⟨hχg, _⟩ := χ.spec (.mk g) (Ω := Ω)
  let χf := χ (.mk f) (Ω := Ω)
  let χg := χ (.mk g) (Ω := Ω)
  -- NOTE: 教科書には以下2つの証明は無し
  have hPB1 : IsPullback f (f ≫ χg) (prod.lift χf χg) (prod.lift (true' Ω) (𝟙 _)) := by
    have w : f ≫ (prod.lift χf χg) = (f ≫ χg) ≫ (prod.lift (true' Ω) (𝟙 _)) := by
      rw [prod.comp_lift, prod.comp_lift, comp_id]
      ext
      . simp only [prod.lift_fst, true']
        rw [hχf.w, ← assoc, terminal.comp_from]
      simp only [prod.lift_snd]
    let cone : PullbackCone (prod.lift χf χg) (prod.lift (true' Ω) (𝟙 _)) := .mk f (f ≫ χg) w
    apply IsPullback.of_isLimit (c := cone)
    apply PullbackCone.IsLimit.mk w (λ s ↦ hχf.lift s.fst (terminal.from _) (by
      have h1 := s.condition
      rw [prod.comp_lift, prod.comp_lift] at h1
      rw [prod.lift_eq_fst h1, ← assoc, terminal.comp_from]))
    . intro s
      rw [hχf.lift_fst]
    . intro s
      have := s.condition
      rw [prod.comp_lift, prod.comp_lift] at this
      rw [← assoc, hχf.lift_fst, prod.lift_eq_snd this, comp_id]
    intro s m hmfst hmsnd
    apply hχf.hom_ext
    . rw [hχf.lift_fst, hmfst]
    simp only [terminal.comp_from]
  have hPB2 : IsPullback g (g ≫ χf) (prod.lift χf χg) (prod.lift (𝟙 _) (true' Ω)) := by
    have w : g ≫ (prod.lift χf χg) = (g ≫ χf) ≫ (prod.lift (𝟙 _) (true' Ω)) := by
      rw [prod.comp_lift, prod.comp_lift, comp_id]
      ext
      simp only [prod.lift_fst]
      rw [hχg.w, ← assoc, terminal.comp_from]
    let cone : PullbackCone (prod.lift χf χg) (prod.lift (𝟙 _) (true' Ω)) := .mk g (g ≫ χf) w
    apply IsPullback.of_isLimit (c := cone)
    apply PullbackCone.IsLimit.mk w (λ s ↦ hχg.lift s.fst (terminal.from _) (by
      have h1 := s.condition
      rw [prod.comp_lift, prod.comp_lift] at h1
      rw [prod.lift_eq_snd h1, ← assoc, terminal.comp_from]))
    . intro s
      rw [hχg.lift_fst]
    . intro s
      have := s.condition
      rw [prod.comp_lift, prod.comp_lift] at this
      rw [← assoc, hχg.lift_fst, prod.lift_eq_fst this, comp_id]
    intro s m hmfst hmsnd
    apply hχg.hom_ext
    . rw [hχg.lift_fst, hmfst]
    simp only [terminal.comp_from]
  have hPB3 := «CH.5».«§5.3».«Fact 2» hPB1 hPB2
  have ⟨h, hPB4⟩ := «Lemma» Ω hPB3
  set α := im Ω <| coprod.desc f g
  set i := im Ω <| coprod.desc
    (prod.lift (true' Ω) (𝟙 _))
    (prod.lift (𝟙 _) (true' Ω))
  have hPB5 : IsPullback i (terminal.from _) «CH.6».«§6.6».disT (TRUE Ω) := (χ.spec ⟨_, i, monoImage Ω _⟩) |>.1
  have hPB := hPB4.paste_vert hPB5
  rw [terminal.comp_from] at hPB
  have ⟨_, huniq⟩ := χ.spec ⟨_, α, monoImage Ω _⟩ (Ω := Ω)
  have := huniq (prod.lift χf χg ≫ «CH.6».«§6.6».disT) hPB |>.symm
  rw [this, ← rf.subset_f.eq]

end «§7.1»

namespace «§7.2»
-- Sub(d) as a latttice

open «CH.4».«§4.1»

variable {d : 𝓒} (Ω : 𝓒) [ElementaryTopos Ω]

section

open «CH.4».«§4.1»

lemma intersection.mk_out (f g : Sub d):
  ⟦subset.mk <| f.out ⋒a(Ω) g.out⟧.out (s := subset.setoid) ≈ (subset.mk <| f.out ⋒a(Ω) g.out) := by
  apply subset.mk_out

lemma union.mk_out (f g : Sub d):
  ⟦subset.mk <| f.out ⋓a(Ω) g.out⟧.out (s := subset.setoid) ≈ (subset.mk <| f.out ⋓a(Ω) g.out) := by
  apply subset.mk_out

end

open «CH.5».«§5.2» in
instance «Theorem 1» {Ω : 𝓒} [ElementaryTopos Ω] : Lattice (Sub d) where
  -- (1)
  -- 教科書曰くrelafive easy to see
  inf f g := ⟦.mk <| f.out ⋒a(Ω) g.out⟧
  inf_le_left f g := by
    let fa := f.out.ar
    let ga := g.out.ar
    have hf : Mono fa := f.out.mono
    have hg : Mono ga := g.out.mono
    let f' := pullback.snd fa ga
    let g' := pullback.fst fa ga
    have ⟨hPB, hf', hg'⟩ := «§7.1».getPullbackCone Ω hf hg
    have := «§7.1».«Theorem 2» Ω fa ga f' g' hPB
    have ⟨⟨i, h₁⟩, ⟨j, h₂⟩⟩ := «CH.4».«§4.2».Theorem
      (.mk <| f' ≫ ga)
      (.mk <| f.out ⋒a(Ω) g.out) |>.mpr this
    dsimp [subset.dom, subset.ar] at i j h₁ h₂
    have ⟨⟨p, hp⟩, _⟩ := intersection.mk_out Ω f g
    use p ≫ j ≫ g'
    rw [assoc, assoc, ← hPB.w, h₂, hp]
  inf_le_right f g := by
    let fa := f.out.ar
    let ga := g.out.ar
    have hf : Mono fa := f.out.mono
    have hg : Mono ga := g.out.mono
    let f' := pullback.snd fa ga
    let g' := pullback.fst fa ga
    have ⟨hPB, hf', hg'⟩ := «§7.1».getPullbackCone Ω hf hg
    have := «§7.1».«Theorem 2» Ω fa ga f' g' hPB
    have ⟨⟨i, h₁⟩, ⟨j, h₂⟩⟩ := «CH.4».«§4.2».Theorem
      (.mk <| f' ≫ ga)
      (.mk <| f.out ⋒a(Ω) g.out) |>.mpr this
    dsimp [subset.dom, subset.ar] at i j h₁ h₂
    have ⟨⟨p, hp⟩, _⟩ := intersection.mk_out Ω f g
    use p ≫ j ≫ f'
    rw [assoc, assoc, h₂, hp]
  le_inf := by
    intro h f g ⟨i, hfh⟩ ⟨j, hgh⟩
    dsimp [subset.ar, subset.dom] at i j hfh hgh
    let fa := f.out.ar
    let ga := g.out.ar
    have hf : Mono fa := f.out.mono
    have hg : Mono ga := g.out.mono
    let f' := pullback.snd fa ga
    let g' := pullback.fst fa ga
    have ⟨hPB, hf', hg'⟩ := «§7.1».getPullbackCone Ω hf hg
    have := «§7.1».«Theorem 2» Ω fa ga f' g' hPB
    have ⟨⟨i₁, h₁⟩, ⟨i₂, h₂⟩⟩ := «CH.4».«§4.2».Theorem
      (.mk <| f' ≫ ga)
      (.mk <| f.out ⋒a(Ω) g.out) |>.mpr this
    have w : i ≫ fa = j ≫ ga := by rw [hfh, hgh]
    have ⟨_, ⟨q, hq⟩⟩ := intersection.mk_out Ω f g
    use pullback.lift i j w ≫ i₁ ≫ q
    rw [assoc, assoc, hq, h₁, ← assoc, pullback.lift_snd i j w, hgh]
  -- (2)
  sup f g := ⟦.mk <| f.out ⋓a(Ω) g.out⟧
  le_sup_left f g := by
    let a := f.out.dom
    let b := g.out.dom
    let fa := f.out.ar
    let ga := g.out.ar
    have hf : Mono fa := f.out.mono
    have hg : Mono ga := g.out.mono
    let i₁ : a ⟶ a ⨿ b := coprod.inl
    have := «§7.1».«Theorem 3» Ω _ hf _ hg
    have ⟨⟨i, h₁⟩, ⟨j, h₂⟩⟩ := «CH.4».«§4.2».Theorem
      ⟨_, im Ω (coprod.desc fa ga), monoImage Ω _⟩
      (.mk <| f.out ⋓a(Ω) g.out) |>.mpr this
    have ⟨_, ⟨q, hq⟩⟩ := union.mk_out Ω f g
    use i₁ ≫ (fstar' Ω <| coprod.desc fa ga) ≫ i ≫ q
    simp only [assoc]
    rw [hq, h₁, epiMonoFactor, coprod.inl_desc]
  le_sup_right f g := by
    let a := f.out.dom
    let b := g.out.dom
    let fa := f.out.ar
    let ga := g.out.ar
    have hf : Mono fa := f.out.mono
    have hg : Mono ga := g.out.mono
    let i₂ : b ⟶ a ⨿ b := coprod.inr
    have := «§7.1».«Theorem 3» Ω _ hf _ hg
    have ⟨⟨i, h₁⟩, ⟨j, h₂⟩⟩ := «CH.4».«§4.2».Theorem
      ⟨_, im Ω (coprod.desc fa ga), monoImage Ω _⟩
      (.mk <| f.out ⋓a(Ω) g.out) |>.mpr this
    have ⟨_, ⟨q, hq⟩⟩ := union.mk_out Ω f g
    use i₂ ≫ (fstar' Ω <| coprod.desc fa ga) ≫ i ≫ q
    simp only [assoc]
    rw [hq, h₁, epiMonoFactor, coprod.inr_desc]
  sup_le := by
    intro f g h ⟨ha', hfh⟩ ⟨hb', hgh⟩
    dsimp [subset.ar, subset.dom] at ha' hb' hfh hgh
    let a := f.out.dom
    let b := g.out.dom
    let c := h.out.dom
    let fa := f.out.ar
    let ga := g.out.ar
    let ha := h.out.ar
    have hf : Mono fa := f.out.mono
    have hg : Mono ga := g.out.mono
    have hh : Mono ha := h.out.mono
    have : coprod.desc fa ga = coprod.desc ha' hb' ≫ ha := by
      dsimp [fa, ga, ha, subset.ar]
      rw [← hfh, ← hgh, coprod.desc_comp]
    let e : 𝓒 := fa' Ω <| coprod.desc ha' hb'
    let j : a ⨿ b ⟶ e := fstar' Ω <| coprod.desc ha' hb'
    let k : e ⟶ c := im Ω <| coprod.desc ha' hb'
    have jepi : Epi j := epiFstar Ω <| coprod.desc ha' hb'
    have khMono : Mono (k ≫ ha) := by
      have : Mono k := monoImage Ω <| coprod.desc ha' hb'
      apply mono_comp
    have : j ≫ k ≫ ha = coprod.desc fa ga := by
      rw [← assoc, epiMonoFactor, this]
    have ⟨u, ⟨⟨_, hu, _⟩, _⟩⟩ := epiMonoUniversal Ω (coprod.desc fa ga) j (k ≫ ha) this

    have := «§7.1».«Theorem 3» Ω _ hf _ hg
    have ⟨⟨i₁, h₁⟩, ⟨i₂, h₂⟩⟩ := «CH.4».«§4.2».Theorem
      ⟨_, im Ω (coprod.desc fa ga), monoImage Ω _⟩
      (.mk <| f.out ⋓a(Ω) g.out) |>.mpr this
    have ⟨⟨p, hp⟩, _⟩ := union.mk_out Ω f g
    use p ≫ i₂ ≫ u ≫ k
    simp only [assoc]
    rw [hu, h₂, hp]

namespace «Corollary»

variable {Ω : 𝓒} [ElementaryTopos Ω]

variable (f g : Sub d)

theorem «(1).1» : f ⊆ g ↔ ⟦.mk (f.out ⋒a(Ω) g.out)⟧ = f := by
  symm
  apply inf_eq_left

theorem «(1).1'» : f.out ⊆ g.out ↔ .mk (f.out ⋒a(Ω) g.out) ≈ f.out := by
  trans
  apply Sub_subset_iff_subs
  symm
  trans
  apply Sub_subset_iff_eqv
  simp only [Quotient.out_eq]
  apply inf_eq_left

theorem «(1).2» : f ⊆ g ↔ ⟦.mk (f.out ⋓a(Ω) g.out)⟧ = g := by
  symm
  apply sup_eq_right

open «CH.6».«§6.6»

theorem «(2)» : f ⊆ g ↔ ∃! h : d ⟶ ImpT (Ω := Ω), h ≫ e = prod.lift (χ f.out) (χ g.out) := by
  trans
  apply «(1).1» (Ω := Ω)
  conv =>
    lhs; rhs; rw [← Quotient.out_eq f]
  trans
  apply Sub_subset_iff_eqv.symm
  trans
  apply «CH.4».«§4.2».Theorem (Ω := Ω)
  rw [← rf.subset_f.eq]
  conv =>
    lhs; rhs; rw [← prod.lift_fst (χ f.out : d ⟶ Ω) (χ g.out : d ⟶ Ω)]
  constructor
  . intro hw
    apply equalizer.existsUnique (prod.lift (χ f.out) (χ g.out)) hw
  intro ⟨h, hh, huniq⟩
  dsimp at hh huniq
  rw [← hh]
  simp only [assoc]
  rw [equalizer.condition]

end «Corollary»

namespace union

lemma comm {f g : subset d} : subset.mk (f ⋓a(Ω) g) ≈ .mk (g ⋓a(Ω) f) := by
  trans
  apply «§7.1».union.sub_out_eq_subset
  apply Sub_subset_iff_eqv.mpr
  have : ⟦subset.mk ((⟦f⟧ : Sub d).out ⋓a(Ω) (⟦g⟧ : Sub d).out)⟧ = (⟦f⟧ ⊔ ⟦g⟧ : Sub d) := by
    rfl
  rw [this, sup_comm]
  apply Sub_subset_iff_eqv.mp
  trans
  apply «§7.1».union.sub_out_eq_subset _ _ _ |>.symm
  apply subset.iseqv.refl

end union

instance «Theorem 2» : BoundedOrder (Sub d) where
  top := ⟦.mk <| 𝟙 d⟧
  le_top := by
    intro f
    let f' := f.out.ar
    let top : subset d := .mk <| 𝟙 d
    have ⟨_, ⟨q, hq⟩⟩ : ⟦top⟧.out ≈ top := top.mk_out
    use f' ≫ q
    rw [assoc, hq, comp_id]
  bot := ⟦.mk <| initial.to d⟧
  bot_le := by
    intro f
    let bot : subset d := .mk <| initial.to d
    have ⟨⟨p, hp⟩, _⟩ : ⟦bot⟧.out ≈ bot := bot.mk_out
    use p ≫ initial.to f.out.dom
    rw [assoc, initial.to_comp, hp]

theorem «Exercise 1» {f : subset d} : f ≈ .mk (𝟙 d) ↔ IsIso f.ar := by
  constructor
  . intro ⟨⟨i, h1⟩, ⟨j, h2⟩⟩
    constructor
    use j
    constructor
    . apply f.mono.right_cancellation
      rw [assoc, h2, id_comp, comp_id]
    apply h2
  intro h
  constructor
  . use f.ar
    rw [comp_id]
  use inv f.ar
  simp

-- distributed latticeの証明は§8.3にて
instance {Ω : 𝓒} [ElementaryTopos Ω] : DistribLattice (Sub d) where
  le_sup_inf := by
    sorry

open «CH.6».«§6.6» «CH.5».«§5.4»
variable {Ω : 𝓒} [ElementaryTopos Ω]

theorem «Theorem 3» (f : subset d)
    : (subset.mk <| f ⋒a(Ω) .mk (∸a(Ω)f)) ≈ (.mk (initial.to d)) := by
  have ⟨hPB1, hPB1uniq⟩ := χ.spec (.mk <| false' (Ω := Ω)) (Ω := Ω)
  have hPB2 := rf.f.PB (Ω := Ω) <| χ f ≫ negT
  let h : (∸o(Ω)f) ⟶ ⊤_ 𝓒 := hPB1.lift ((∸a(Ω)f) ≫ χ f) (terminal.from (∸o(Ω)f)) (by
    have := hPB2.w
    dsimp [«§7.1».complement.ob]
    rw [assoc, «§7.1».complement.ar]
    dsimp [negT] at *
    rw [this])
  have hPB3 : IsPullback (∸a(Ω)f) h (χ f) false' := hPB2.of_bot' hPB1
  have hf : Mono f.ar := f.mono
  have ⟨p, g, _, hp, hg, hPB⟩ := «§7.1».«Theorem 2'» Ω f.ar (∸a(Ω)f)
  have h₁ : g ≫ f.ar ≫ χ f (Ω := Ω) = terminal.from _ ≫ false' := by
    have : h = terminal.from _ := by ext
    rw [← assoc, ← hPB.w, assoc, hPB3.w, this, ← assoc, terminal.comp_from]
  have h₂ : g ≫ f.ar ≫ χ f (Ω := Ω) = (g ≫ terminal.from _) ≫ true := by
    rw [χ.spec f (Ω := Ω) |>.1.w, assoc]
  have ⟨hPB', huniq⟩ := χ.spec (.mk <| initial.to (⊤_ 𝓒)) (Ω := Ω)
  let k : (f ⋒o(Ω) (.mk (∸a(Ω)f))) ⟶ ⊥_ 𝓒 := hPB'.lift (terminal.from _) (g ≫ terminal.from _) (by rw [← h₁, ← h₂])
  have hcz : (f ⋒o(Ω) (.mk (∸a(Ω)f))) ≅ (⊥_ 𝓒) := «CH.3».«§3.16».«Theorem 1».«(2)» k
  have h₃ : k ≫ initial.to d = f ⋒a(Ω) (.mk (∸a(Ω)f)) := by
    have initC : IsInitial (f ⋒o(Ω) (.mk (∸a(Ω)f))) := .ofIso initialIsInitial hcz.symm
    have : k = initC.to _ := by apply initC.hom_ext
    rw [this, initC.to_comp]
    apply initC.hom_ext
  have h₄ : (subset.mk <| f ⋒a(Ω) (.mk (∸a(Ω)f))) ⊆ (.mk (initial.to d)) := ⟨k, h₃⟩
  constructor
  . apply h₄
  apply Sub_subset_iff_subs.mpr
  apply OrderBot.bot_le (⟦.mk (f ⋒a(Ω) (.mk (∸a(Ω)f)))⟧ : Sub d)

-- NOTE: 後で使う
lemma «Theorem 3'» {d : 𝓒} (f : subset d) : IsPullback (initial.to _) (initial.to _) f.ar (∸a(Ω) f) := by
  have := f.mono
  have ⟨p, q, hp, hpmono, hqmono, hPB⟩ := «§7.1».«Theorem 2'» Ω f.ar (∸a(Ω) f)
  have ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := «Theorem 3» f (Ω := Ω)
  dsimp [subset.ar, subset.dom] at i j hi hj
  have h₂ : IsIso i := by
    constructor
    use j
    constructor
    . apply cancel_mono (f ⋒a(Ω) .mk (∸a(Ω) f)) |>.mp
      rw [id_comp, assoc, hj, hi]
    apply cancel_mono (initial.to d) |>.mp
    rw [id_comp, assoc, hi, hj]
  apply hPB.flip.of_iso (asIso i) (.refl _) (.refl _) (.refl _)
  . rw [Iso.refl_hom, comp_id, asIso_hom]
    have h₁ : initial.to f.dom ≫ f.ar = initial.to d := by ext
    apply cancel_mono f.ar |>.mp
    rw [assoc, h₁, hi, ← hPB.w, hp]
  . rw [Iso.refl_hom, comp_id, asIso_hom]
    have h₁ : initial.to _ ≫ (∸a(Ω) f) = initial.to d := by ext
    apply cancel_mono (∸a(Ω) f) |>.mp
    rw [assoc, h₁, hi, hp]
  . simp
  simp

theorem «Theorem 4» : subset.mk false' ≈ .mk (∸a(Ω) (.mk (true (Ω := Ω)))) := by
  apply «CH.4».«§4.2».Theorem _ _ (Ω := Ω) |>.mpr
  rw [← rf.subset_f.eq, «CH.4».«§4.2».«Exercise 1», id_comp, negT]

lemma iso_pbcone_is_pb {a b c d a' : 𝓒} {f : a ⟶ b} {g : a ⟶ c} {f' : b ⟶ d} {g' : c ⟶ d} {i : a' ⟶ a}
  (h : IsIso i) (hPB : IsPullback f g f' g') : IsPullback (i ≫ f) (i ≫ g) f' g' := by
  apply hPB.of_iso (fst' := i ≫ f) (snd' := i ≫ g) (f' := f') (g' := g')
    (asIso i).symm (.refl _) (.refl _) (.refl _) (by simp) (by simp) (by simp) (by simp)

open «§7.1» in
lemma intersection.ext {f g f' g' : subset d} (h₁ : f ≈ f') (h₂ : g ≈ g')
    : subset.mk (f ⋒a(Ω) g) ≈ .mk (f' ⋒a(Ω) g') := by
  apply «CH.4».«§4.2».Theorem _ _ (Ω := Ω) |>.mpr
  have h₁ : χ f = χ f' := «CH.4».«§4.2».Theorem _ _ (Ω := Ω) |>.mp h₁
  have h₂ : χ g = χ g' := «CH.4».«§4.2».Theorem _ _ (Ω := Ω) |>.mp h₂
  rw [← rf.subset_f.eq, ← rf.subset_f.eq, h₁, h₂]

open «§7.1» in
lemma intersection.sub_out_eq_subset (f g : subset d)
    : subset.mk (f ⋒a(Ω) g) ≈ .mk ((⟦f⟧ : Sub d).out ⋒a(Ω) (⟦g⟧ : Sub d).out) := by
  have h₁ : f ≈ (⟦f⟧ : Sub d).out := by
    apply subset.iseqv.symm
    apply f.mk_out
  have h₂ : g ≈ (⟦g⟧ : Sub d).out := by
    apply subset.iseqv.symm
    apply g.mk_out
  apply intersection.ext h₁ h₂

theorem «Theorem 5» (f : subset Ω) (h : IsCompl (⟦.mk <| true (Ω := Ω)⟧ : Sub Ω) ⟦f⟧) : f ≈ .mk false' := by
  have ⟨hsup, hinf⟩ := «CH.6».«§6.4».complemented.mp h
  have hf : Mono f.ar := f.mono
  let a := f.dom
  have hPB : IsPullback (initial.to a) (terminal.from _) f.ar true := by
    have ⟨p, q, _, hp, hq, hPB⟩ := «§7.1».«Theorem 2'» Ω true f.ar
    have ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := Quotient.exact hinf
    have ⟨_, jiso⟩ := equiv_iso hi hj
    dsimp [subset.dom] at i j
    have ⟨⟨o₁, ho₁⟩, ⟨o₂, ho₂⟩⟩ := intersection.sub_out_eq_subset (.mk true) f (Ω := Ω)
    dsimp [subset.dom] at o₁ o₂
    have ⟨_, hiso₂⟩ := equiv_iso ho₁ ho₂
    have jiso : IsIso (j ≫ o₂) := by apply IsIso.comp_isIso
    have := iso_pbcone_is_pb jiso hPB
    have h₁ : j = initial.to _ := by ext
    have h₂ : q = terminal.from _ := by ext
    rw [h₁, h₂, terminal.comp_from, initial.to_comp, initial.to_comp] at this
    apply this
  have : f.ar = false a := by
    have ⟨hPB1, huniq⟩ := χ.spec (.mk <| initial.to a) (Ω := Ω)
    dsimp [subset.ar, subset.dom] at huniq
    have := huniq f.ar hPB
    rw [«CH.5».«§5.4».«Exercise 3»] at this
    apply this
  have h₂ : (⟦.mk true⟧ : Sub Ω) ⊔ ⟦f⟧ ⊆ ⟦.mk true⟧ ⊔ ⟦.mk false'⟧ := by
    have hf₁ : f ⊆ .mk false' := ⟨terminal.from a, this.symm⟩
    have : (⟦f⟧ : Sub Ω) ⊆ ⟦.mk false'⟧ := by
      apply Sub_subset_iff_subs.mp hf₁
    apply sup_le_sup_left (α := Sub Ω) this ⟦.mk true⟧

  have h₃ : (⟦.mk true⟧ : Sub Ω) ⊔ ⟦.mk false'⟧ = ⊤ := by
    apply le_antisymm
    . apply le_top
    rw [← hsup]
    apply h₂
  have h₄ : (⟦.mk true⟧ : Sub Ω) ⊓ ⟦.mk false'⟧ = ⊥ := by
    apply Quotient.sound
    trans
    apply intersection.sub_out_eq_subset _ _ |>.symm
    trans
    apply intersection.ext (subset.iseqv.refl _) «Theorem 4»
    apply «Theorem 3»

  have := «CH.6».«§6.4».«Exercise 1» ⟨hinf, h₄, hsup, h₃⟩
  apply Sub_subset_iff_eqv.mpr this

end «§7.2»

namespace «§7.3»
-- Boolean topoi

open «CH.4».«§4.1» «CH.5».«§5.4»

abbrev Boolean (𝓒 : Type*) [Category 𝓒] (Ω : 𝓒) [ElementaryTopos Ω]
  := ∀ d : 𝓒, BooleanAlgebra (Sub d)

namespace «Theorem 1»
variable (Ω : 𝓒) [ElementaryTopos Ω]

lemma «§3.6.ex3» {a : 𝓒} (f : ⊤_ 𝓒 ⟶ a) : Mono f := «CH.3».«§3.6».Excercises.«3» 𝓒 f

abbrev «(1)» := Boolean 𝓒 Ω
abbrev «(2)» := BooleanAlgebra (Sub Ω)
abbrev «(3)» := ∃ f : Sub Ω, IsCompl (⟦.mk <| true (Ω := Ω)⟧ : Sub Ω) f
abbrev «(4)» := IsCompl (⟦.mk <| true (Ω := Ω)⟧ : Sub Ω) ⟦.mk false'⟧
abbrev «(5)» := (⟦.mk <| true (Ω := Ω)⟧ : Sub Ω) ⊔ ⟦.mk false'⟧ = ⊤
abbrev «(6)» := ClassicalTopos 𝓒
abbrev «(7)» := IsSubobjectClassifier (coprod.inl : ⊤_ 𝓒 ⟶ (⊤_ 𝓒) ⨿ (⊤_ 𝓒))

def «(1)→(2)» : «(1)» Ω → «(2)» Ω := by
  intro h
  apply h Ω

def «(2)→(3)» : «(2)» Ω → «(3)» Ω := by
  intro h
  let x : Sub Ω := ⟦.mk <| true (Ω := Ω)⟧
  use xᶜ
  -- apply isCompl_compl
  sorry

theorem «(3)→(4)» : «(3)» Ω → «(4)» Ω := by
  intro ⟨f', hf⟩
  let f := f'.out
  rw [← Quotient.out_eq f'] at hf
  have := Quotient.sound <| «§7.2».«Theorem 5» f hf
  rw [this] at hf
  apply hf

theorem «(4)→(5)» : «(4)» Ω → «(5)» Ω := by
  intro h
  apply «CH.6».«§6.4».complemented.mp h |>.1

lemma comp_subset_eq {a d : 𝓒} (f : subset d) (k : a ⟶ f.dom) [IsIso k] [Mono (k ≫ f.ar)]
    : f ≈ .mk (k ≫ f.ar) := by
  constructor
  . use inv k
    dsimp [subset.ar]
    rw [← assoc, IsIso.inv_hom_id, id_comp]
  use k

lemma subset_ar_eq_eqv {a d : 𝓒} {f g : a ⟶ d} [Mono f] [Mono g] (h : f = g) : subset.mk f ≈ .mk g := by
  constructor
  . use 𝟙 _
    dsimp [subset.ar, subset.dom]
    rw [id_comp, h]
  use 𝟙 _
  dsimp [subset.ar, subset.dom]
  rw [id_comp, h]

open «CH.5».«§5.2» in
theorem «(5)→(6)» : «(5)» Ω → «(6)» Ω := by
  intro h
  let ctf : (⊤_ 𝓒) ⨿ ⊤_ 𝓒 ⟶ Ω := coprod.desc true false'
  have hctfMono : Mono ctf := «CH.5».«§5.4».«Theorem 3»

  have h1: subset.mk (coprod.desc (true (Ω := Ω)) false') ≈ .mk (.mk true ⋓a(Ω) .mk false') := by
    have ⟨k, ⟨hkstar, hkim, hkiso⟩, huniq⟩ := «CH.5».«§5.2».epiMonoUniversal (Ω := Ω) ctf (𝟙 _) ctf (id_comp _)
    have h₁ := «CH.4».«§4.2».Theorem _ _ |>.mpr («§7.1».«Theorem 3» Ω (true (Ω := Ω)) («§3.6.ex3» Ω _) false' («§3.6.ex3» Ω _))
    have : Mono (k ≫ ctf) := by
      have : Mono k := IsIso.mono_of_iso k
      apply mono_comp
    have h₂ := comp_subset_eq (.mk ctf) k
    have : Mono (im Ω ctf) := monoImage Ω ctf
    have h₃ := subset_ar_eq_eqv hkim
    dsimp [subset.ar] at h₂
    have h₄ : subset.mk ctf ≈ .mk (im Ω ctf) := subset.iseqv.trans h₂ h₃
    apply subset.iseqv.trans h₄ h₁

  have h2 : subset.mk (.mk true ⋓a(Ω) .mk false') ≈ .mk (𝟙 Ω) := by
    trans
    apply «§7.1».union.sub_out_eq_subset
    apply Sub_subset_iff_eqv.mpr
    apply h

  have h3 : subset.mk (coprod.desc (true (Ω := Ω)) false') ≈ .mk (𝟙 Ω) := subset.iseqv.trans h1 h2
  apply «§7.2».«Exercise 1» (f := .mk <| coprod.desc (true (Ω := Ω)) false') |>.mp h3

lemma iso_pb_is_pb {a b c d d' : 𝓒} {f : a ⟶ b} {g : a ⟶ c} {f' : b ⟶ d} {g' : c ⟶ d} {i : d ⟶ d'}
  {f'i : b ⟶ d'} {g'i : c ⟶ d'} (hf : f' ≫ i = f'i) (hg : g' ≫ i = g'i)
  (h : IsIso i) (hPB : IsPullback f g f' g') : IsPullback f g f'i g'i := by
  apply hPB.of_iso (.refl _) (.refl _) (.refl _) (asIso i)
    (by simp) (by simp) (by simp [hf]) (by simp [hg])

theorem «(6)→(7)» : «(6)» Ω → «(7)» Ω := by
  intro h
  let ctf : (⊤_ 𝓒) ⨿ ⊤_ 𝓒 ⟶ Ω := coprod.desc true false'
  have : IsIso ctf := h
  constructor
  intro d f
  have ⟨hPB, huniq⟩ := χ.spec f (Ω := Ω)
  let χ' : d ⟶ (⊤_ 𝓒) ⨿ ⊤_ 𝓒 := χ f ≫ inv ctf
  use χ'
  constructor
  . have hf : χ f ≫ inv ctf = χ' := rfl
    -- NOTE: 教科書ではΩと同型ならなんでもいけるみたいな書きっぷりだったが
    -- 下記のhg相当の条件が一般的な対象では成り立たないと思われる
    have hg : true (Ω := Ω) ≫ inv ctf = coprod.inl := by simp; rw [coprod.inl_desc]
    have : IsIso (inv ctf) := by
      constructor
      use ctf
      constructor
      . rw [IsIso.inv_hom_id]
      rw [IsIso.hom_inv_id]
    apply iso_pb_is_pb hf hg this hPB
  intro y hPB
  have hf : y ≫ ctf = y ≫ ctf := rfl
  have hg : coprod.inl ≫ ctf = true (Ω := Ω) := by rw [coprod.inl_desc]
  have := huniq (y ≫ ctf) <| iso_pb_is_pb hf hg this hPB
  dsimp [χ']
  rw [← this]
  rw [assoc, IsIso.hom_inv_id, comp_id]

theorem «Lemma» (Ω : 𝓒) [ElementaryTopos Ω] : IsPullback (initial.to (⊤_ 𝓒)) (initial.to (⊤_ 𝓒)) coprod.inr coprod.inl := by
  have w₁ : initial.to (⊤_ 𝓒) ≫ coprod.inr = initial.to (⊤_ 𝓒) ≫ coprod.inl := by
    simp only [initial.to_comp]
  have hPO : IsPushout (initial.to (⊤_ 𝓒)) (initial.to (⊤_ 𝓒)) coprod.inr coprod.inl := by
    apply IsPushout.of_hasBinaryCoproduct' _ _ |>.flip
  have ⟨hPBχ, huniq⟩ := χ.spec (.mk <| initial.to (⊤_ 𝓒)) (Ω := Ω)
  have w₂ : initial.to (⊤_ 𝓒) ≫ false' = initial.to (⊤_ 𝓒) ≫ true (Ω := Ω) := by
    conv =>
      rhs; rw [← init_top_eq_terminal_bot]
    have := hPBχ.w
    dsimp [subset.ar, subset.dom] at this
    apply this
  let k : (⊤_ 𝓒) ⨿ ⊤_ 𝓒 ⟶ Ω := hPO.desc false' true w₂
  let csq : CommSq (initial.to (⊤_ 𝓒)) (initial.to (⊤_ 𝓒)) coprod.inr coprod.inl := ⟨w₁⟩
  apply IsPullback.of_isLimit' csq
  apply PullbackCone.IsLimit.mk w₁ (λ s ↦ hPBχ.lift s.fst s.snd (by
    have hk₁ : true (Ω := Ω) = coprod.inl ≫ k := by
      rw [hPO.inr_desc]
    have hk₂ : χ (.mk <| initial.to _) = coprod.inr ≫ k := by
      rw [hPO.inl_desc]
    rw [hk₁, hk₂, ← assoc, s.condition, assoc]))
  . intro s
    rw [hPBχ.lift_fst]
  . intro s
    conv =>
      lhs; congr; rfl; rw [← init_top_eq_terminal_bot]
    rw [hPBχ.lift_snd]
  intro s m hmfst hmsnd
  apply hPBχ.hom_ext
  . dsimp [subset.ar]
    rw [hmfst, hPBχ.lift_fst]
  dsimp [subset.ar, subset.dom]
  rw [← init_top_eq_terminal_bot] at hmsnd
  rw [hmsnd, hPBχ.lift_snd]

open «CH.6».«§6.6» in
lemma coprod_epi {d : 𝓒} (f : Sub d) (h : «(7)» Ω)
    : Epi (coprod.desc f.out.ar (⟦.mk (∸a(Ω) f.out)⟧ : Sub d).out.ar) := by
  let a : 𝓒 := f.out.dom
  let nf : Sub d := ⟦.mk (∸a(Ω) f.out)⟧

  let t' := h.hasSubobjectClassifier
  let ts : subset Ω := .mk true
  let t's : subset _ := .mk (coprod.inl : ⊤_ 𝓒 ⟶ (⊤_ 𝓒) ⨿ ⊤_ 𝓒)
  let p : (⊤_ 𝓒) ⨿ ⊤_ 𝓒 ⟶ Ω := HasSubobjectClassifier.Ω_axiom t's |>.choose
  let q := (t'.Ω_axiom ts).choose
  have hPBp : IsPullback coprod.inl (terminal.from _) p true := HasSubobjectClassifier.Ω_axiom t's |>.choose_spec.1
  have hPBq : IsPullback true (terminal.from _) q coprod.inl := (t'.Ω_axiom ts).choose_spec.1
  have hp : IsIso p := HasSubobjectClassifier.uniqueUpToIso' _ t' |>.choose
  have hpq : inv p = q := HasSubobjectClassifier.uniqueUpToIso' _ t' |>.choose_spec

  have h₂ : false' = coprod.inr ≫ p := by
    have ⟨_, hPB1uniq⟩ := χ.spec (.mk <| initial.to (⊤_ 𝓒)) (Ω := Ω)
    symm
    apply hPB1uniq
    dsimp [subset.ar, subset.dom]
    have := «Lemma» Ω |>.paste_vert hPBp
    rw [«CH.3».«§3.6».terminal_id, comp_id] at this
    rw [«CH.5».«§5.4».init_top_eq_terminal_bot]
    apply this

  let k : (⊤_ 𝓒) ⨿ ⊤_ 𝓒 ⟶ Ω := coprod.desc true false'
  have hkp : k = p := by
    apply coprod.hom_ext
    . rw [coprod.inl_desc, hPBp.w, «CH.3».«§3.6».terminal_id, id_comp]
    rw [coprod.inr_desc]
    apply h₂
  have : IsIso k := by
    rw [hkp]
    apply hp
  have ⟨invp, hpb, _⟩ := t'.Ω_axiom <| .mk <| true (Ω := Ω)

  let χf' : d ⟶ (⊤_ 𝓒) ⨿ ⊤_ 𝓒 := χ f.out ≫ q
  have hqk : q = inv k := by
    rw [← hpq]
    apply IsIso.inv_eq_inv.mpr
    apply hkp.symm

  have hPB₁ : IsPullback f.out.ar (terminal.from _) χf' coprod.inl := by
    have ⟨hf, _⟩ := χ.spec f.out (Ω := Ω)
    have := hf.paste_vert hPBq
    dsimp [subset.dom] at this
    dsimp [χf']
    rw [«CH.3».«§3.6».terminal_id, comp_id] at this
    apply this
  have hPB₂ : IsPullback nf.out.ar (terminal.from _) χf' coprod.inr := by
    have ⟨hPB1, hPB1uniq⟩ := χ.spec (.mk <| false' (Ω := Ω)) (Ω := Ω)
    have hPB2 := rf.f.PB (Ω := Ω) <| χ f.out ≫ negT
    let g := hPB1.lift ((∸a(Ω) f.out) ≫ χ f.out) (terminal.from _) (by
      have := hPB2.w
      dsimp [«§7.1».complement.ar, «§7.1».complement.ob, negT] at *
      rw [assoc]
      apply this)
    have hPB3 : IsPullback (∸a(Ω) f.out) g (χ f.out (Ω := Ω)) (coprod.inr ≫ p) := by
      rw [← h₂]
      apply hPB2.of_bot' hPB1
    have hPB4 : IsPullback (∸a(Ω) f.out) g χf' coprod.inr := by
      apply hPB3.of_iso (.refl _) (.refl _) (.refl _) (asIso p).symm
        (by simp) (by simp) (by simp [χf', hpq]) (by simp)
    have : g = terminal.from _ := by ext
    rw [this] at hPB4
    apply χ.Sub_subset (.mk (∸a(Ω) f.out)) χf' coprod.inr hPB4
  have hPB₃ := «CH.5».«§5.3».«Fact 2» hPB₁ hPB₂ |>.flip
  rw [coprod.desc_inl_inr] at hPB₃
  apply «CH.5».«§5.3».«Fact 1» hPB₃

lemma em {d : 𝓒} (h : «(7)» Ω) (f : Sub d) :
    (⟦f.out⟧ : Sub d) ⊔ ⟦.mk (∸a(Ω) f.out)⟧ = ⊤ := by
  apply «CH.4».«§4.1».Sub_subset_iff_eqv.mp
  let nf : Sub d := ⟦.mk (∸a(Ω) f.out)⟧
  constructor
  . use (⟦f.out⟧ : Sub d).out ⋓a(Ω) nf.out
    dsimp [subset.ar]
    rw [comp_id]
  let a : 𝓒 := f.out.dom
  let na : 𝓒 := nf.out.dom
  let fnf : a ⨿ na ⟶ d := coprod.desc f.out.ar nf.out.ar
  have hfnf : Epi fnf := coprod_epi Ω f h
  have ⟨k, ⟨_, hkim, _⟩, _⟩ :=
    «CH.5».«§5.2».epiMonoUniversal Ω fnf fnf (𝟙 _) (by rw [comp_id])
  have ⟨⟨p, hp⟩, _⟩ :=
    «CH.4».«§4.2».Theorem _ _
      |>.mpr («§7.1».«Theorem 3» Ω f.out.ar f.out.mono nf.out.ar nf.out.mono)
  have ⟨_, ⟨q, hq⟩⟩ :=
    «§7.1».union.ext (Ω := Ω) f.out.mk_out (subset.iseqv.refl nf.out)
  let j := inv k ≫ p ≫ q
  use inv k ≫ p ≫ q
  simp only [assoc]
  rw [hq, hp]
  dsimp [subset.ar]
  rw [IsIso.inv_comp_eq, hkim]

def Sub.isBooleanAlgebra {d : 𝓒} (h : ∀ f : Sub d, (⟦f.out⟧ : Sub d) ⊔ ⟦.mk (∸a(Ω) f.out)⟧ = ⊤)
    : BooleanAlgebra (Sub d) := by
  have : ComplementedLattice (Sub d) := by
    constructor
    intro f
    let a : 𝓒 := f.out.dom
    let nf : Sub d := ⟦.mk (∸a(Ω) f.out)⟧
    let na : 𝓒 := nf.out.dom
    rw [← Quotient.out_eq f]
    use nf
    apply «CH.6».«§6.4».complemented.mpr
    constructor
    . apply h f
    apply «CH.4».«§4.1».Sub_subset_iff_eqv.mp
    trans
    have : nf.out ≈ .mk (∸a(Ω) f.out) := by
      dsimp [nf]
      apply subset.mk_out
    apply «§7.2».intersection.ext (Ω := Ω) f.out.mk_out this
    apply «§7.2».«Theorem 3»
  apply DistribLattice.booleanAlgebraOfComplemented

def «(7)→(1)» : «(7)» Ω → «(1)» Ω := by
  intro h d
  apply Sub.isBooleanAlgebra (Ω := Ω)
  apply em Ω h

end «Theorem 1»

end «§7.3»

namespace «§7.4»
-- Internal vs External

variable (Ω : 𝓒) [ElementaryTopos Ω]

open «§7.3».«Theorem 1» in
theorem «Theorem 1» : «§7.3».Boolean 𝓒 Ω → ∀ α : Φ, 𝓒 (Ω)⊨ α ∨ₚₗ ~ₚₗ α := by
  intro h α V'
  let Vα : ⊤_ 𝓒 ⟶ Ω := «CH.6».«§6.7».V V' α
  let a : 𝓒 := rf.a Vα
  let f : a ⟶ ⊤_ 𝓒 := rf.f Vα
  have : χ (rf.subset_f Vα) = Vα := rf.subset_f.eq Vα |>.symm
  let fs : Sub (⊤_ 𝓒) := ⟦rf.subset_f Vα⟧
  have hfs : χ fs.out = Vα := by
    rw [χ.sub_out_eq_subset (rf.subset_f Vα), ← rf.subset_f.eq]

  let nfs : Sub (⊤_ 𝓒) := ⟦.mk (∸a(Ω) fs.out)⟧
  have h1 : (subset.mk (fs.out ⋓a(Ω) nfs.out)) ≈ (.mk <| 𝟙 _) := by
    have h7 : «(7)» Ω := by
      apply «(6)→(7)»
      apply «(5)→(6)»
      apply «(4)→(5)»
      apply «(3)→(4)»
      apply «(2)→(3)»
      apply «(1)→(2)»
      apply h
    trans
    apply subset.iseqv.symm <|
      «§7.1».union.ext (Ω := Ω) fs.out.mk_out (subset.iseqv.refl nfs.out)
    apply «CH.4».«§4.1».Sub_subset_iff_eqv.mpr <| em Ω h7 fs
  have h2 : χ (.mk (fs.out ⋓a(Ω) nfs.out)) = true (Ω := Ω) := by
    conv =>
      rhs; rw [← «CH.4».«§4.2».«Exercise 2'» (𝓒 := 𝓒)]
    apply «CH.4».«§4.2».Theorem _ _ |>.mp h1
  have h3 : χ (.mk (fs.out ⋓a(Ω) nfs.out)) = «CH.6».«§6.7».V V' (α ∨ₚₗ ~ₚₗ α) :=
    calc
      χ (.mk (fs.out ⋓a(Ω) nfs.out))
      _ = χ (.mk (fs.out ⋓a(Ω) .mk (∸a(Ω) fs.out))) := by apply «CH.4».«§4.2».Theorem _ _ |>.mp («§7.1».union.ext (Ω := Ω) (subset.iseqv.refl _) (subset.mk (∸a(Ω) fs.out)).mk_out)
      _ = χ fs.out ∪(Ω) (χ fs.out ≫ «CH.6».«§6.6».negT) := by rw [«§7.1».union.eq, «§7.1».complement.eq]
      _ = Vα ∪(Ω) (Vα ≫ «CH.6».«§6.6».negT) := by rw [hfs]
      _ = «CH.6».«§6.7».V V' (α ∨ₚₗ ~ₚₗ α) := by dsimp
  rw [← h2, ← h3]

namespace «Theorem 2»

abbrev «(1)» := ∀ α : Φ, (𝓒 (Ω)⊨ α) ↔ ⊢ᶜˡ α
abbrev «(2)» := ∀ α : Φ, 𝓒 (Ω)⊨ α ∨ₚₗ ~ₚₗ α
abbrev «(3)» := BooleanAlgebra (Sub (⊤_ 𝓒))

open «CH.6».«§6.3».«PL-sentence» in
theorem «(1)→(2)» : «(1)» Ω → «(2)» Ω := by
  -- Clearly (1) implies (2)
  intro h α
  rw [h (α ∨ₚₗ ~ₚₗ α)]
  apply Cinf.axiom' (CL.Axiom.XII _)

def «(2)→(3)» : «(2)» Ω → «(3)» Ω := by
  intro h
  apply «CH.7».«§7.3».«Theorem 1».Sub.isBooleanAlgebra (Ω := Ω)
  intro f
  let V' : Φ₀ → element Ω := λ _ ↦ χ f.out
  let π₀ : Φ₀ := ⟨0⟩
  have := h (.var π₀) V'
  let nf : Sub (⊤_ 𝓒) := ⟦.mk (∸a(Ω) f.out)⟧
  have h1 : χ (.mk (f.out ⋓a(Ω) nf.out)) = χ (.mk <| 𝟙 (⊤_ 𝓒)) (Ω := Ω) :=
    calc
      χ (.mk (f.out ⋓a(Ω) nf.out))
      _ = χ (.mk (f.out ⋓a(Ω) .mk (∸a(Ω) f.out))) := by apply «CH.4».«§4.2».Theorem _ _ |>.mp («§7.1».union.ext (Ω := Ω) (subset.iseqv.refl _) (subset.mk (∸a(Ω) f.out)).mk_out)
      _ = χ f.out ∪(Ω) (χ f.out ≫ «CH.6».«§6.6».negT) := by rw [«§7.1».union.eq, «§7.1».complement.eq]
      _ = V' π₀ ∪(Ω) (V' π₀ ≫ «CH.6».«§6.6».negT) := by dsimp [V']
      _ = «CH.6».«§6.7».V V' ((.var π₀) ∨ₚₗ ~ₚₗ (.var π₀)) := by dsimp
      _ = true (Ω := Ω) := h (.var π₀) V'
      _ = χ (.mk (𝟙 _)) := «CH.4».«§4.2».«Exercise 2'» (𝓒 := 𝓒) |>.symm
  apply «CH.4».«§4.1».Sub_subset_iff_eqv.mp
  trans
  apply «§7.1».union.ext (Ω := Ω) f.out.mk_out (subset.iseqv.refl nf.out)
  apply «CH.4».«§4.2».Theorem _ _ |>.mpr h1

theorem «(3)→(1)» : «(3)» Ω → «(1)» Ω := by
  intro h α
  constructor
  . apply «CH.6».«§6.7».Lemma.«Theorem 2»
  -- I~XIの公理の証明が必要、後でやるとのこと
  -- Theorem 1からXIIが証明される
  sorry

end «Theorem 2»

-- NOTE: 教科書だとiff条件だがLeanのiffは左右どちらもPropである必要があり、BooleanAlgebraはPropではないためiffにてきない
open «CH.6».«§6.6» «CH.5».«§5.4» «CH.7».«§7.3» in
def «Theorem 3» : BooleanAlgebra (Sub Ω) → prod.lift (𝟙 Ω) negT ≫ disT = true' Ω := by
  intro h
  have h1 : subset.mk (.mk (true (Ω := Ω)) ⋓a(Ω) .mk false') ≈ .mk (𝟙 Ω) := by
    have := «Theorem 1».«(4)→(5)» _ <| «Theorem 1».«(3)→(4)» _ <| «Theorem 1».«(2)→(3)» _ h
    trans
    apply «§7.1».union.ext (Ω := Ω) (subset.mk_out _) (subset.mk_out _) |>.symm
    apply «CH.4».«§4.1».Sub_subset_iff_eqv.mpr this
  have h2 : subset.mk (.mk (true (Ω := Ω)) ⋓a(Ω) .mk false') ≈ .mk (𝟙 Ω) ↔ prod.lift (𝟙 Ω) negT ≫ disT = true' Ω :=
    calc
      subset.mk (.mk (true (Ω := Ω)) ⋓a(Ω) .mk false') ≈ .mk (𝟙 Ω)
      _ ↔ χ (.mk (.mk (true (Ω := Ω)) ⋓a(Ω) .mk false')) = χ (.mk (𝟙 Ω)) (Ω := Ω) := «CH.4».«§4.2».Theorem _ _
      _ ↔ (χ (.mk (true (Ω := Ω))) ∪(Ω) χ (.mk false')) = χ (.mk (𝟙 Ω)) (Ω := Ω) := by rw [«§7.1».union.eq]
      _ ↔ prod.lift (𝟙 Ω) negT ≫ disT = true' Ω := by rw [«CH.4».«§4.2».«Exercise 1», «CH.4».«§4.2».«Exercise 2», negT]
  apply h2.mp h1

namespace «Exercise 2»

variable (α : Φ)

theorem I : 𝓒 (Ω)⊨ α ⊃ₚₗ (α ∧ₚₗ α) := by
  intro V'
  sorry

end «Exercise 2»

end «§7.4»

namespace «§7.5»
-- Implication and its implications

variable (Ω : 𝓒) [ElementaryTopos Ω] {d : 𝓒}

namespace implication

variable (f g : subset d)

abbrev ob : 𝓒 := rf.a <| χ f ⇒(Ω) χ g
abbrev ar : ob Ω f g ⟶ d  := rf.f <| χ f ⇒(Ω) χ g

notation:80 f " ⇰o(" Ω ") " g => ob Ω f g
notation:80 f " ⇰a(" Ω ") " g => ar Ω f g

lemma eq (f g : subset d) : χ (.mk <| f ⇰a(Ω) g) = χ f ⇒(Ω) χ g := by
  rw [← rf.subset_f.eq]

lemma ext {f g f' g' : subset d} (h₁ : f ≈ f') (h₂ : g ≈ g')
    : subset.mk (f ⇰a(Ω) g) ≈ .mk (f' ⇰a(Ω) g') := by
  apply «CH.4».«§4.2».Theorem _ _ (Ω := Ω) |>.mpr
  have h₁ : χ f = χ f' := «CH.4».«§4.2».Theorem _ _ (Ω := Ω) |>.mp h₁
  have h₂ : χ g = χ g' := «CH.4».«§4.2».Theorem _ _ (Ω := Ω) |>.mp h₂
  rw [← rf.subset_f.eq, ← rf.subset_f.eq, h₁, h₂]

end implication

namespace «Lemma 1»

variable (f g h : subset d)

theorem «(1)» : subset.mk (f ⋒a(Ω) h) ≈ .mk (g ⋒a(Ω) h) ↔ h.ar ≫ χ f (Ω := Ω) = h.ar ≫ χ g := by
  have := f.mono
  have := g.mono
  have := h.mono
  have ⟨h₁, p, hh₁, h₁mono, _, hPB₁⟩ := «CH.7».«§7.1».«Theorem 2'» Ω f.ar h.ar
  have ⟨h₂, q, hh₂, h₂mono, _, hPB₂⟩ := «CH.7».«§7.1».«Theorem 2'» Ω g.ar h.ar
  have ⟨hPBf, _⟩ := χ.spec f (Ω := Ω)
  have ⟨hPBg, _⟩ := χ.spec g (Ω := Ω)

  have h₁χ : h.ar ≫ χ f = χ (.mk h₁) (Ω := Ω) := by
    have ⟨_, huniq⟩ := χ.spec (.mk h₁) (Ω := Ω)
    apply huniq
    have := hPB₁.paste_vert hPBf
    rw [terminal.comp_from] at this
    apply this

  have h₂χ : h.ar ≫ χ g = χ (.mk h₂) (Ω := Ω) := by
    have ⟨_, huniq⟩ := χ.spec (.mk h₂) (Ω := Ω)
    apply huniq
    have := hPB₂.paste_vert hPBg
    rw [terminal.comp_from] at this
    apply this

  have h1 : h.ar ≫ χ f (Ω := Ω) = h.ar ≫ χ g ↔ subset.mk h₁ ≈ .mk h₂ := by
    rw [h₁χ, h₂χ]
    symm
    apply «CH.4».«§4.2».Theorem
  have h2 : subset.mk (f ⋒a(Ω) h) ≈ .mk (g ⋒a(Ω) h) ↔ subset.mk h₁ ≈ .mk h₂ := by
    -- 教科書とは証明の順番が逆
    constructor
    . intro ⟨⟨k, hk⟩, ⟨kinv, hkinv⟩⟩
      dsimp [subset.ar, subset.dom] at k hk kinv hkinv
      constructor
      . use k
        apply cancel_mono h.ar |>.mp
        rw [assoc, ← hh₁, ← hh₂, hk]
      use kinv
      apply cancel_mono h.ar |>.mp
      rw [assoc, ← hh₁, ← hh₂, hkinv]
    intro ⟨⟨k, hk⟩, ⟨kinv, hkinv⟩⟩
    dsimp [subset.ar, subset.dom] at k hk kinv hkinv
    constructor
    . use k
      rw [← hk, assoc, ← hh₂] at hh₁
      apply hh₁.symm
    use kinv
    rw [← hkinv, assoc, ← hh₁] at hh₂
    apply hh₂.symm
  trans
  apply h2
  apply h1.symm

theorem «(2)» : (χ f ∩(Ω) χ h) = (χ g ∩(Ω) χ h) ↔ h.ar ≫ χ f (Ω := Ω) = h.ar ≫ χ g :=
  calc
    (χ f ∩(Ω) χ h) = (χ g ∩(Ω) χ h)
    _ ↔ χ (.mk (f ⋒a(Ω) h)) = χ (.mk (g ⋒a(Ω) h)) (Ω := Ω) := by simp only [«CH.7».«§7.1».intersection.eq]
    _ ↔ subset.mk (f ⋒a(Ω) h) ≈ .mk (g ⋒a(Ω) h) := «CH.4».«§4.2».Theorem _ _ |>.symm
    _ ↔ h.ar ≫ χ f (Ω := Ω) = h.ar ≫ χ g := «(1)» Ω f g h

end «Lemma 1»

theorem «Corollary» (f g h : Sub d) :
    f ⊓ h ⊆ g ↔ h.out.ar ≫ χ (f ⊓ g).out = h.out.ar ≫ χ f.out (Ω := Ω) :=
  calc
    f ⊓ h ⊆ g
    _ ↔ (f ⊓ h) ⊓ g = f ⊓ h := by symm; apply inf_eq_left
    _ ↔ (f ⊓ g) ⊓ h = f ⊓ h := by rw [inf_assoc, inf_comm h g, ← inf_assoc]
    _ ↔ subset.mk ((f ⊓ g).out ⋒a(Ω) h.out) ≈ .mk (f.out ⋒a(Ω) h.out) := by rw [Sub_subset_iff_eqv]; rfl
    _ ↔ h.out.ar ≫ χ (f ⊓ g).out = h.out.ar ≫ χ f.out (Ω := Ω) := «Lemma 1».«(1)» _ _ _ _

theorem Corollary' (f g h : subset d) : subset.mk (f ⋒a(Ω) h) ⊆ g ↔ h.ar ≫ χ (.mk (f ⋒a(Ω) g)) = h.ar ≫ χ f (Ω := Ω) := by
  have h1 : subset.mk (f ⋒a(Ω) h) ⊆ g ↔ (⟦f⟧ : Sub d) ⊓ ⟦h⟧ ⊆ ⟦g⟧ := by
    trans
    apply Sub_subset_iff_subs
    have := Sub_subset_iff_eqv.mp <| «§7.2».intersection.ext (Ω := Ω) f.mk_out h.mk_out
    rw [← this]
    rfl
  have h2 : (⟦f⟧ : Sub d) ⊓ ⟦h⟧ ⊆ ⟦g⟧ ↔ subset.mk ((⟦f⟧ ⊓ ⟦g⟧ : Sub d).out ⋒a(Ω) (⟦h⟧ : Sub d).out) ≈ .mk ((⟦f⟧ : Sub d).out ⋒a(Ω) (⟦h⟧ : Sub d).out) :=
    calc
      ⟦f⟧ ⊓ ⟦h⟧ ⊆ ⟦g⟧
      _ ↔ (⟦f⟧ ⊓ ⟦h⟧) ⊓ ⟦g⟧ = (⟦f⟧ ⊓ ⟦h⟧ : Sub d) := by symm; apply inf_eq_left
      _ ↔ (⟦f⟧ ⊓ ⟦g⟧) ⊓ ⟦h⟧ = ⟦f⟧ ⊓ ⟦h⟧ := by rw [inf_assoc, inf_comm ⟦h⟧ ⟦g⟧, ← inf_assoc]
      _ ↔ subset.mk ((⟦f⟧ ⊓ ⟦g⟧ : Sub d).out ⋒a(Ω) (⟦h⟧ : Sub d).out) ≈ .mk ((⟦f⟧ : Sub d).out ⋒a(Ω) (⟦h⟧ : Sub d).out) := by rw [Sub_subset_iff_eqv]; rfl
  have h3 : subset.mk ((⟦f⟧ ⊓ ⟦g⟧ : Sub d).out ⋒a(Ω) (⟦h⟧ : Sub d).out) ≈ .mk ((⟦f⟧ : Sub d).out ⋒a(Ω) (⟦h⟧ : Sub d).out)
      ↔ subset.mk (.mk (f ⋒a(Ω) g) ⋒a(Ω) h) ≈ .mk (f ⋒a(Ω) h) := by
    trans
    apply Sub_subset_iff_eqv
    symm
    trans
    apply Sub_subset_iff_eqv
    have h1 := «§7.2».intersection.ext (Ω := Ω) f.mk_out h.mk_out
    rw [Sub_subset_iff_eqv.mp h1]
    have h2 : (⟦f⟧ ⊓ ⟦g⟧ : Sub d).out ≈ subset.mk (f ⋒a(Ω) g) := by
      trans
      apply subset.mk_out
      apply «§7.2».intersection.ext f.mk_out g.mk_out
    have h3 := «§7.2».intersection.ext (Ω := Ω) h2 h.mk_out
    rw [Sub_subset_iff_eqv.mp h3]
  trans
  apply h1
  trans
  apply h2
  trans
  apply h3
  apply «Lemma 1».«(1)»

namespace «Theorem 1»

variable (f g h : subset d)

open «CH.6».«§6.6» in
theorem «(1)» : h ⊆ .mk (f ⇰a(Ω) g) ↔ .mk (f ⋒a(Ω) h) ⊆ g := by
  have hPB1 : IsPullback (f ⇰a(Ω) g) (terminal.from _) (prod.lift (χ f) (χ g) ≫ impT) true := rf.f.PB <| χ f ⇒(Ω) χ g
  have ⟨hPB2, _⟩ := χ.spec (Ω := Ω) (.mk (e (Ω := Ω)))
  have hPB2 : IsPullback e (terminal.from _) impT true := hPB2
  let j : (f ⇰o(Ω) g) ⟶ ImpT (Ω := Ω) := hPB2.lift ((f ⇰a(Ω) g) ≫ prod.lift (χ f) (χ g)) (terminal.from _) (by rw [assoc, hPB1.w])
  have hPB3 : IsPullback (f ⇰a(Ω) g) j (prod.lift (χ f) (χ g)) e := hPB1.of_bot' hPB2
  -- NOTE: 教科書では逆の証明無し
  have h1 : h ⊆ .mk (f ⇰a(Ω) g) ↔ ∃ k : h.dom ⟶ (f ⇰o(Ω) g), h.ar ≫ prod.lift (χ f) (χ g) = k ≫ j ≫ e := by
    constructor
    . intro ⟨k, hk⟩
      use k
      rw [← hPB3.w, ← assoc, hk]
    intro ⟨k, hk⟩
    let k' := hPB3.lift h.ar (k ≫ j) (by rw [assoc, hk])
    use k'
    apply hPB3.lift_fst h.ar (k ≫ j) (by rw [assoc, hk])
  -- NOTE: 教科書では逆の証明無し
  have h2 : (∃ k : h.dom ⟶ (f ⇰o(Ω) g), h.ar ≫ prod.lift (χ f) (χ g) = k ≫ j ≫ e)
      ↔ h.ar ≫ χ (.mk (f ⋒a(Ω) g))  = h.ar ≫ χ f (Ω := Ω) := by
    constructor
    . intro ⟨k, hk⟩
      have : e ≫ conT = e ≫ (prod.fst : Ω ⨯ Ω ⟶ Ω) := equalizer.condition conT prod.fst
      rw [«CH.7».«§7.1».intersection.eq]
      conv => rhs; rw [← prod.lift_fst (χ f (Ω := Ω)) (χ g (Ω := Ω))]
      simp only [← assoc, hk]
      simp only [assoc, this]
    intro h'
    rw [«CH.7».«§7.1».intersection.eq] at h'
    let k' := equalizer.lift (h.ar ≫ prod.lift (χ f) (χ g)) (f := conT) (g := (prod.fst : Ω ⨯ Ω ⟶ Ω)) (by
      rw [assoc, h', assoc, prod.lift_fst])
    let k := hPB3.lift h.ar k' (by symm; apply equalizer.lift_ι)
    use k
    rw [← hPB3.lift_fst h.ar k' (by symm; apply equalizer.lift_ι), assoc, hPB3.w]
  trans
  apply h1
  trans
  apply h2
  symm
  apply Corollary' Ω f g h

theorem «(2)» : f ⊆ g ↔ subset.mk (f ⇰a(Ω) g) ≈ .mk (𝟙 d) := by
  constructor
  . intro h'
    have h1 :∀ h : subset d, ⟦f⟧ ⊓ ⟦h⟧ ⊆ (⟦g⟧ : Sub d):= by
      intro h
      calc
        ⟦f⟧ ⊓ ⟦h⟧
        _ ≤ (⟦f⟧ : Sub d) := by apply inf_le_left
        _ ≤ ⟦g⟧ := Sub_subset_iff_subs.mp h'
    have h2 : ∀ h : subset d, h ⊆ .mk (f ⇰a(Ω) g) := by
      intro h
      apply «(1)» _ f g h |>.mpr
      have := Sub_subset_iff_eqv.mp («§7.2».intersection.sub_out_eq_subset f h (Ω := Ω))
      apply Sub_subset_iff_subs.mpr
      rw [this]
      apply h1
    apply Sub_subset_iff_eqv.mpr
    apply isTop_iff_eq_top.mp
    intro h
    rw [← Quotient.out_eq h]
    apply Sub_subset_iff_subs.mp
    apply h2
  intro h'
  have h1 : f ⊆ .mk (f ⇰a(Ω) g) := by
    apply Sub_subset_iff_subs.mpr
    rw [Sub_subset_iff_eqv.mp h']
    apply «§7.2».«Theorem 2» Ω |>.le_top
  have h2 : subset.mk (f ⋒a(Ω) f) ⊆ g := «(1)» _ f g f |>.mp h1
  have h2' : (⟦f⟧ : Sub d) ⊓ ⟦f⟧ ⊆ ⟦g⟧ := by
    have := Sub_subset_iff_eqv.mp («§7.2».intersection.sub_out_eq_subset f f (Ω := Ω))
    have h2 := Sub_subset_iff_subs.mp h2
    rw [this] at h2
    apply h2
  rw [inf_idem] at h2'
  apply Sub_subset_iff_subs.mpr h2'

theorem «(3)» : f ⊆ g ↔ (χ f ⇒(Ω) χ g) = true' d := by
  trans
  apply «(2)» Ω
  trans
  apply «CH.4».«§4.2».Theorem (Ω := Ω)
  rw [implication.eq]
  rw [«CH.4».«§4.2».«Exercise 2''»]

end «Theorem 1»

open «CH.6».«§6.6» in
theorem «Exercise» (f g : subset d) : f ⊆ g ↔ subset.mk (f ⇰a(Ω) g) ≈ .mk (𝟙 d) := by
  trans
  apply Sub_subset_iff_subs
  trans
  apply «§7.2».Corollary.«(2)» (Ω := Ω)
  simp only [χ.sub_out_eq_subset]
  have hPB1 : IsPullback (f ⇰a(Ω) g) (terminal.from _) (prod.lift (χ f) (χ g) ≫ impT) true := rf.f.PB <| χ f ⇒(Ω) χ g
  have ⟨hPB2, _⟩ := χ.spec (Ω := Ω) (.mk (e (Ω := Ω)))
  have hPB2 : IsPullback e (terminal.from _) impT true := hPB2
  constructor
  . intro ⟨h, hh, huniq⟩
    constructor
    . use f ⇰a(Ω) g
      dsimp [subset.ar]
      rw [comp_id]
    have h₁ : prod.lift (χ f) (χ g) ≫ impT = true' d (Ω := Ω) := by
      rw [← hh, assoc, hPB2.w, ← assoc, terminal.comp_from]
    let k : d ⟶ (f ⇰o(Ω) g) := hPB1.lift (𝟙 d) (terminal.from d) (by rw [id_comp, h₁])
    use k
    dsimp [subset.ar]
    rw [hPB1.lift_fst]
  intro ⟨_, ⟨k, hk⟩⟩
  dsimp [subset.dom, subset.ar] at k hk
  let j : (f ⇰o(Ω) g) ⟶ ImpT (Ω := Ω) := hPB2.lift ((f ⇰a(Ω) g) ≫ prod.lift (χ f) (χ g)) (terminal.from _) (by rw [assoc, hPB1.w])
  use k ≫ j
  have h₂ : (k ≫ j) ≫ e = prod.lift (χ f) (χ g) := by
    rw [assoc, hPB2.lift_fst, ← assoc, hk, id_comp]
  constructor
  . apply h₂
  intro m hm
  apply hPB2.hom_ext
  . rw [h₂, hm]
  ext

namespace «Corollary»

theorem «(1).1» : subset.mk (.mk (𝟙 d) ⇰a(Ω) .mk (𝟙 d)) ≈ .mk (𝟙 d) := by
  have h : subset.mk (𝟙 d) ⊆ .mk (𝟙 d) := by
    use 𝟙 _
    rw [id_comp]
  apply «Theorem 1».«(2)» _ _ _ |>.mp h

theorem «(1).2» : subset.mk (.mk (initial.to d) ⇰a(Ω) .mk (𝟙 d)) ≈ .mk (𝟙 d) := by
  have h : subset.mk (initial.to d) ⊆ .mk (𝟙 d) := by
    use initial.to d
    ext
  apply «Theorem 1».«(2)» _ _ _ |>.mp h

theorem «(1).3» : subset.mk (.mk (initial.to d) ⇰a(Ω) .mk (initial.to d)) ≈ .mk (𝟙 d) := by
  have h : subset.mk (initial.to d) ⊆ .mk (initial.to d) := by
    use 𝟙 _
    ext
  apply «Theorem 1».«(2)» _ _ _ |>.mp h

-- NOTE: 本当はSub dの束の条件から導く方がシンプルだし教科書に準拠しているが、うまい定義をしなかった以上下記のようにした
-- TODO: subsetとSubの入れ替えをスムーズにする方法を考える
theorem «(2)» : subset.mk (.mk (𝟙 d) ⇰a(Ω) .mk (initial.to d)) ≈ .mk (initial.to d) := by
  have h₁ : subset.mk (.mk (𝟙 d) ⇰a(Ω) .mk (initial.to d)) ⊆ .mk (.mk (𝟙 d) ⇰a(Ω) .mk (initial.to d)) := by
    use 𝟙 _
    rw [id_comp]
  have h₂ := «Theorem 1».«(1)» _ _ _ _ |>.mp h₁
  have h₃ : ∀ f : Sub d, ⊤ ⊓ f = f := by
    intro f
    apply top_inf_eq
  have h₄ := Sub_subset_iff_eqv.mpr <| h₃ ⟦.mk (.mk (𝟙 d) ⇰a(Ω) .mk (initial.to d))⟧
  have h₅ :subset.mk (.mk (𝟙 _) ⋒a(Ω) .mk (.mk (𝟙 d) ⇰a(Ω) .mk (initial.to d))) ≈ .mk ((⊤ : Sub d).out ⋒a(Ω) (⟦.mk (.mk (𝟙 d) ⇰a(Ω) .mk (initial.to d))⟧ : Sub d).out) := by
    apply «§7.2».intersection.sub_out_eq_subset
  have := subset.iseqv.trans h₅ h₄
  trans
  apply this.symm
  constructor
  . apply h₂
  use initial.to _
  ext

end «Corollary»

namespace «Lemma 2»

theorem «(1)» {X : Type*} [Lattice X] {m n a b: X}
    («(i)» : ∀ x : X, x ≤ m ↔ a ⊓ x ≤ b)
    («(ii)» : ∀ x : X, x ≤ n ↔ a ⊓ x ≤ b)
  : m = n := by
  have h₁ : m ≤ n := by
    apply «(ii)» m |>.mpr
    apply «(i)» m |>.mp (le_refl m)
  have h₂ : n ≤ m := by
    apply «(i)» n |>.mpr
    apply «(ii)» n |>.mp (le_refl _)
  apply le_antisymm h₁ h₂

theorem «(2)» {B : Type*} [BooleanAlgebra B] {x a b : B}
    : x ≤ aᶜ ⊔ b ↔ a ⊓ x ≤ b := by
  have h₁ : ∀ {x y z : B} (_ : x ≤ z), y ⊓ x ≤ y ⊓ z := by
    intro x y z h
    apply inf_le_inf_left y h
  have h₂ : a ⊓ (aᶜ ⊔ b) ≤ b :=
    calc
      a ⊓ (aᶜ ⊔ b)
      _ = (a ⊓ aᶜ) ⊔ (a ⊓ b) := inf_sup_left _ _ _
      _ = ⊥ ⊔ (a ⊓ b) := by rw [inf_compl_self]
      _ = a ⊓ b := bot_sup_eq _
      _ ≤ b := inf_le_right
  constructor
  . intro h
    calc
      a ⊓ x
      _ ≤ a ⊓ (aᶜ ⊔ b) := h₁ h
      _ ≤ b := h₂
  intro h
  calc
    x
    _ = ⊤ ⊓ x := by rw [top_inf_eq]
    _ = (aᶜ ⊔ a) ⊓ x := by rw [sup_comm, sup_compl_eq_top]
    _ = (aᶜ ⊓ x) ⊔ (a ⊓ x) := inf_sup_right _ _ _
    _ ≤ (aᶜ ⊓ x) ⊔ b := sup_le_sup_left h _
    _ ≤ aᶜ ⊔ b := sup_le_sup_right inf_le_left _

end «Lemma 2»

namespace «Theorem 2»

abbrev «(1)» := «§7.3».Boolean 𝓒
abbrev «(2)» := ∀ {d : 𝓒}(f g : Sub d), subset.mk (f.out ⇰a(Ω) g.out) ≈ .mk (.mk (∸a(Ω) f.out) ⋓a(Ω) g.out)
abbrev «(3)» := ∀ (f g : Sub Ω), subset.mk (f.out ⇰a(Ω) g.out) ≈ .mk (.mk (∸a(Ω) f.out) ⋓a(Ω) g.out)
abbrev «(4)» := subset.mk (.mk (true (Ω := Ω)) ⇰a(Ω) .mk true) ≈ .mk (.mk true ⋓a(Ω) .mk «CH.5».«§5.4».false')

theorem «(1)→(2)» : «(1)» Ω → «(2)» Ω := by
  intro h₁ d f g
  apply Sub_subset_iff_eqv.mpr
  apply «Lemma 2».«(1)» (a := f) (b := g)
  . intro h
    have h₂ : h = ⟦h.out⟧ := Quotient.out_eq h |>.symm
    rw [h₂]
    trans
    apply Sub_subset_iff_subs.symm
    trans
    apply «Theorem 1».«(1)» Ω f.out g.out h.out
    trans
    apply Sub_subset_iff_subs
    have h₃ : ⟦g.out⟧ = g := Quotient.out_eq g
    rw [h₃, ← h₂]
    rfl
  intro h
  have h₂ : h = ⟦h.out⟧ := Quotient.out_eq h |>.symm
  rw [h₂]
  have h₄ : .mk (∸a(Ω) f.out) ≈ fᶜ.out := sorry
  have := Sub_subset_iff_eqv.mp <| «§7.1».union.ext h₄ (subset.iseqv.refl g.out) (Ω := Ω)
  rw [this]
  -- TODO: BooleanAlgebraでのsupとLatticeのsupが食い違っているっぽい
  -- apply «Lemma 2».«(2)» (x := ⟦h.out⟧) (a := f) (b := g)
  -- apply Sub_subset_iff_subs.symm
  sorry

theorem «(2)→(3)» : «(2)» Ω → «(3)» Ω := by
  -- obvious
  intro h
  apply h

theorem «(3)→(4)» : «(3)» Ω → «(4)» Ω := by
  intro h
  have h₁ : (⟦.mk (true (Ω := Ω))⟧ : Sub Ω).out ≈ subset.mk true := subset.mk_out _
  have h₂ := implication.ext Ω h₁ h₁
  have h₃ := h ⟦.mk (true (Ω := Ω))⟧ ⟦.mk (true (Ω := Ω))⟧
  dsimp [«(4)»]
  trans
  apply subset.iseqv.trans h₂.symm h₃
  trans
  apply «§7.2».union.comm
  apply «§7.1».union.ext
  . apply subset.mk_out
  . trans
    apply «§7.1».complement.ext Ω (subset.mk_out _)
    apply «§7.2».«Theorem 4» (Ω := Ω) |>.symm

def «(4)→(1)» : «(4)» Ω → «(1)» Ω := by
  intro h
  have : subset.mk (.mk (true (Ω := Ω)) ⇰a(Ω) .mk true) ≈ .mk (𝟙 Ω) := by
    apply «Theorem 1».«(2)» _ _ _ |>.mp
    use 𝟙 _
    rw [id_comp]
  have : «§7.3».«Theorem 1».«(5)» Ω := by
    apply Sub_subset_iff_eqv.mp
    trans
    apply «§7.1».union.sub_out_eq_subset _ _ _ |>.symm
    trans
    apply h.symm
    apply this
  apply «§7.3».«Theorem 1».«(7)→(1)» _ <| «§7.3».«Theorem 1».«(6)→(7)» _ <| «§7.3».«Theorem 1».«(5)→(6)» _ this

end «Theorem 2»

end «§7.5»

namespace «§7.6»
-- Filling two gaps

open «CH.5».«§5.4»

variable (Ω : 𝓒) [ElementaryTopos Ω]

namespace «1.»

abbrev «1'» (d : 𝓒) : subset d := .mk (𝟙 d)
abbrev «0'» (d : 𝓒) : subset d := .mk (initial.to d)

lemma inf_eq_intersection {d : 𝓒} {f g h : subset d} : ⟦f⟧ ⊓ ⟦g⟧ = (⟦h⟧ : Sub d) → χ (.mk (f ⋒a(Ω) g)) = χ h (Ω := Ω) := by
  intro h'
  apply «CH.4».«§4.2».Theorem _ _ |>.mp
  trans
  apply «§7.2».intersection.sub_out_eq_subset
  apply Sub_subset_iff_eqv.mpr
  apply h'

theorem and_tf : (true ∩(Ω) false') = false' :=
  calc
    true ∩(Ω) false'
    _ = χ («1'» (⊤_ 𝓒)) ∩(Ω) χ («0'» _ (⊤_ 𝓒)) := by rw [«CH.4».«§4.2».«Exercise 2'»]
    _ = χ (.mk («1'» (⊤_ 𝓒) ⋒a(Ω) «0'» Ω (⊤_ 𝓒))) := by rw [← rf.subset_f.eq]
    _ = χ («0'» Ω (⊤_ 𝓒)) := inf_eq_intersection _ (inf_bot_eq _)
    _ = false' := rfl

theorem and_tt : (true ∩(Ω) true) = true (Ω := Ω) :=
  calc
    true ∩(Ω) true
    _ = χ («1'» (⊤_ 𝓒)) ∩(Ω) χ («1'» (⊤_ 𝓒)) := by rw [«CH.4».«§4.2».«Exercise 2'»]
    _ = χ (.mk («1'» (⊤_ 𝓒) ⋒a(Ω) «1'» (⊤_ 𝓒))) := by rw [← rf.subset_f.eq]
    _ = χ («1'» (⊤_ 𝓒)) := inf_eq_intersection _ (inf_idem _)
    _ = true (Ω := Ω) := «CH.4».«§4.2».«Exercise 2'»

theorem and_ft : (false' ∩(Ω) true) = false' :=
  calc
    false' ∩(Ω) true
    _ = χ («0'» Ω (⊤_ 𝓒)) ∩(Ω) χ («1'» (⊤_ 𝓒)) := by rw [«CH.4».«§4.2».«Exercise 2'»]
    _ = χ (.mk («0'» Ω (⊤_ 𝓒) ⋒a(Ω) «1'» (⊤_ 𝓒))) := by rw [← rf.subset_f.eq]
    _ = χ («0'» Ω (⊤_ 𝓒)) := inf_eq_intersection _ (bot_inf_eq _)
    _ = false' := rfl

theorem and_ff : (false' ∩(Ω) false') = false' :=
  calc
    false' ∩(Ω) false'
    _ = χ (.mk («0'» Ω (⊤_ 𝓒) ⋒a(Ω) «0'» Ω (⊤_ 𝓒))) := by rw [← rf.subset_f.eq]
    _ = χ («0'» Ω (⊤_ 𝓒)) := inf_eq_intersection _ (inf_idem _)

theorem imp_tf : (true ⇒(Ω) false') = false' :=
  calc
    true ⇒(Ω) false'
    _ = χ («1'» (⊤_ 𝓒)) ⇒(Ω) χ («0'» Ω (⊤_ 𝓒)) := by rw [«CH.4».«§4.2».«Exercise 2'»]
    _ = χ (.mk («1'» (⊤_ 𝓒) ⇰a(Ω) «0'» Ω (⊤_ 𝓒))) := by rw [← rf.subset_f.eq]
    _ = χ («0'» Ω (⊤_ 𝓒)) := «CH.4».«§4.2».Theorem _ _ |>.mp («§7.5».Corollary.«(2)» _)
    _ = false' := rfl

theorem imp_ft : (false' ⇒(Ω) true) = true (Ω := Ω) :=
  calc
    false' ⇒(Ω) true
    _ = χ («0'» Ω (⊤_ 𝓒)) ⇒(Ω) χ («1'» (⊤_ 𝓒)) := by rw [«CH.4».«§4.2».«Exercise 2'»]
    _ = χ (.mk («0'» Ω (⊤_ 𝓒) ⇰a(Ω) «1'» (⊤_ 𝓒))) := by rw [← rf.subset_f.eq]
    _ = χ («1'» (⊤_ 𝓒)) := «CH.4».«§4.2».Theorem _ _ |>.mp («§7.5».Corollary.«(1).2» _)
    _ = true (Ω := Ω) := «CH.4».«§4.2».«Exercise 2'»

theorem imp_tt : (true ⇒(Ω) true) = true (Ω := Ω) :=
  calc
    true ⇒(Ω) true
    _ = χ («1'» (⊤_ 𝓒)) ⇒(Ω) χ («1'» (⊤_ 𝓒)) := by rw [«CH.4».«§4.2».«Exercise 2'»]
    _ = χ (.mk («1'» (⊤_ 𝓒) ⇰a(Ω) «1'» (⊤_ 𝓒))) := by rw [← rf.subset_f.eq]
    _ = χ («1'» (⊤_ 𝓒)) := «CH.4».«§4.2».Theorem _ _ |>.mp («§7.5».Corollary.«(1).1» _)
    _ = true (Ω := Ω) := «CH.4».«§4.2».«Exercise 2'»

theorem imp_ff : (false' ⇒(Ω) false') = true (Ω := Ω) :=
  calc
    false' ⇒(Ω) false'
    _ = χ (.mk («0'» Ω (⊤_ 𝓒) ⇰a(Ω) «0'» Ω (⊤_ 𝓒))) := by rw [← rf.subset_f.eq]
    _ = χ («1'» (⊤_ 𝓒)) := «CH.4».«§4.2».Theorem _ _ |>.mp («§7.5».Corollary.«(1).3» _)
    _ = true (Ω := Ω) := «CH.4».«§4.2».«Exercise 2'»

namespace «Exercise»

lemma sup_eq_union {d : 𝓒} {f g h : subset d} : ⟦f⟧ ⊔ ⟦g⟧ = (⟦h⟧ : Sub d) → χ (.mk (f ⋓a(Ω) g)) = χ h (Ω := Ω) := by
  intro h'
  apply «CH.4».«§4.2».Theorem _ _ |>.mp
  trans
  apply «§7.1».union.sub_out_eq_subset
  apply Sub_subset_iff_eqv.mpr
  apply h'

theorem or_tt : (true ∪(Ω) true) = true (Ω := Ω) :=
  calc
    true ∪(Ω) true
    _ = χ («1'» (⊤_ 𝓒)) ∪(Ω) χ («1'» (⊤_ 𝓒)) := by rw [«CH.4».«§4.2».«Exercise 2'»]
    _ = χ (.mk («1'» (⊤_ 𝓒) ⋓a(Ω) «1'» (⊤_ 𝓒))) := by rw [← rf.subset_f.eq]
    _ = χ («1'» (⊤_ 𝓒)) := sup_eq_union _ (sup_idem _)
    _ = true (Ω := Ω) := «CH.4».«§4.2».«Exercise 2'»

theorem or_tf : (true ∪(Ω) false') = true (Ω := Ω) :=
  calc
    true ∪(Ω) false'
    _ = χ («1'» (⊤_ 𝓒)) ∪(Ω) χ («0'» Ω (⊤_ 𝓒)) := by rw [«CH.4».«§4.2».«Exercise 2'»]
    _ = χ (.mk («1'» (⊤_ 𝓒) ⋓a(Ω) «0'» Ω (⊤_ 𝓒))) := by rw [← rf.subset_f.eq]
    _ = χ («1'» (⊤_ 𝓒)) := sup_eq_union _ (top_sup_eq _)
    _ = true (Ω := Ω) := «CH.4».«§4.2».«Exercise 2'»

theorem or_ft : (false' ∪(Ω) true) = true (Ω := Ω) :=
  calc
    false' ∪(Ω) true
    _ = χ («0'» Ω (⊤_ 𝓒)) ∪(Ω) χ («1'» (⊤_ 𝓒)) := by rw [«CH.4».«§4.2».«Exercise 2'»]
    _ = χ (.mk («0'» Ω (⊤_ 𝓒) ⋓a(Ω) «1'» (⊤_ 𝓒))) := by rw [← rf.subset_f.eq]
    _ = χ («1'» (⊤_ 𝓒)) := sup_eq_union _ (sup_top_eq _)
    _ = true (Ω := Ω) := «CH.4».«§4.2».«Exercise 2'»

theorem or_ff : (false' ∪(Ω) false') = false' :=
  calc
    false' ∪(Ω) false'
    _ = χ (.mk («0'» Ω (⊤_ 𝓒) ⋓a(Ω) «0'» Ω (⊤_ 𝓒))) := by rw [← rf.subset_f.eq]
    _ = χ («0'» Ω (⊤_ 𝓒)) := sup_eq_union _ (sup_idem _)

end «Exercise»

end «1.»

namespace «2.»

open «CH.7».«§7.3» in
def «(6)→(1)» : ClassicalTopos 𝓒 Ω → Boolean 𝓒 Ω := by
  intro h
  apply «Theorem 1».«(7)→(1)»
  apply «Theorem 1».«(6)→(7)» _ h

theorem «§5.4.5 if» : (ClassicalTopos 𝓒 Ω ∧ ∀ a : 𝓒, nonZero a → nonEmpty a) → WellPointed 𝓒 := by
  intro ⟨hCL, hze⟩
  have h1 : nonDegenerate 𝓒 := by
    -- TODO: 教科書に証明が無い
    intro h
    sorry
  constructor
  . exact h1
  intro a b f g hnfg
  let c : 𝓒 := equalizer f g
  let h : c ⟶ a := equalizer.ι f g
  have hh : Mono h := equalizer.ι_mono
  let hs : subset a := .mk h

  -- NOTE: 教科書ではBooleanから排中律を持ってくるが、上掲の問題からBooleanを使いたくない
  -- そのため«§7.3».«Theorem 1».emを使う
  -- have := «(6)→(1)» Ω hCL
  -- have h₁ : (⟦.mk h⟧ : Sub a)ᶜ = ⟦.mk (∸a(Ω) hs)⟧ := sorry

  have h₁ := «§7.3».«Theorem 1».«(6)→(7)» Ω hCL

  have h₂ : nonZero (∸o(Ω) hs) := by
    intro hiso
    have : subset.mk (∸a(Ω) hs) ≈ .mk (initial.to a) := by
      constructor
      . use inv (initial.to (∸o(Ω) hs))
        dsimp [subset.ar]
        rw [hiso.inv_comp_eq, initial.to_comp]
      use initial.to _
      ext
    have h₁ : hs ≈ .mk (𝟙 a) := by
      calc
        hs
        _ ≈ .mk (hs ⋓a(Ω) .mk (initial.to a)) := by
          apply subset.iseqv.symm
          apply subset.iseqv.trans
          apply «§7.1».union.sub_out_eq_subset
          apply Sub_subset_iff_eqv.mpr
          apply sup_bot_eq
        _ ≈ .mk (hs ⋓a(Ω) .mk (∸a(Ω) hs)) := «§7.1».union.ext Ω (subset.iseqv.refl _) (this.symm)
        _ ≈ .mk (𝟙 a) := by
          trans
          apply «§7.1».union.ext Ω hs.mk_out.symm («§7.1».complement.ext Ω hs.mk_out.symm)
          trans
          apply «§7.1».union.sub_out_eq_subset
          apply «CH.4».«§4.1».Sub_subset_iff_eqv.mpr
          apply «§7.3».«Theorem 1».em _ h₁
    have h₂ : IsIso h := «§7.2».«Exercise 1».mp h₁
    have h₃ : Epi h := by apply h₂.epi_of_iso
    apply hnfg
    apply h₃.left_cancellation
    apply equalizer.condition f g
  let y : ⊤_ 𝓒 ⟶ (∸o(Ω) hs) := Classical.choice <| hze _ h₂
  let x : ⊤_ 𝓒 ⟶ a := y ≫ ∸a(Ω) hs
  use x
  intro hfg
  let z : ⊤_ 𝓒 ⟶ c := equalizer.lift x hfg
  have h₃ : z ≫ h = x := equalizer.lift_ι x hfg

  have h₄ : ⊥_ 𝓒 ≅ ⊤_ 𝓒 := by
    have hPB := «§7.2».«Theorem 3'» hs (Ω := Ω) |>.flip
    let k := hPB.lift y z (by rw [h₃])
    apply «CH.3».«§3.16».«Theorem 1».«(2)» k |>.symm
  have h₅ := h₄.isIso_hom
  have h₆ : initial.to _ = h₄.hom := by ext
  apply h1
  rw [h₆]
  apply h₅

end «2.»

end «§7.6»

namespace «§7.7»
-- Extensionality revisited

variable (Ω : 𝓒) [ElementaryTopos Ω] {d : 𝓒}

theorem «Theorem 1» (f g : subset d) (x : element d) : x ∈ subset.mk (f ⋒a(Ω) g) ↔ x ∈ f ∧ x ∈ g := by
  have := f.mono
  have := g.mono
  have ⟨p, q, hp, hpmono, hqmono, hPB⟩ := «§7.1».«Theorem 2'» Ω f.ar g.ar
  simp only [subset.mk_eq] at p q hp hPB hpmono hqmono
  constructor
  . intro ⟨k, hk⟩
    constructor
    . use k ≫ q
      rw [assoc, ← hPB.w, ← hp, hk]
    use k ≫ p
    rw [assoc, ← hp, hk]
  intro ⟨⟨k, hk⟩, ⟨h, hh⟩⟩
  let t := hPB.lift h k (by rw [hk, hh])
  use t
  dsimp [subset.ar]
  rw [← hh, ← hPB.lift_fst h k (by rw [hk, hh]), assoc, ← hp]

variable (𝓒)
abbrev extensional : Prop
  := ∀ {d : 𝓒} (f g : subset d), f ⊆ g ↔ ∀ x : element d, x ∈ f → x ∈ g
variable {𝓒}

open «CH.5».«§5.4»

theorem «Theorem 2» : extensional 𝓒 Ω ↔ WellPointed 𝓒 := by
  constructor
  . intro hex
    constructor
    . sorry
    intro a b f g
    contrapose
    simp only [ne_eq, not_exists, not_not]
    intro hfg

    let c : 𝓒 := equalizer f g
    let h : c ⟶ a := equalizer.ι f g
    have hh : Mono h := equalizer.ι_mono
    let hs : subset a := .mk h
    have h₁ : ∀ x : element a, x ∈ subset.mk (𝟙 a) → x ∈ hs := by
      intro x ⟨k, hk⟩
      have hxfg := hfg x
      let t := equalizer.lift x hxfg
      have : t ≫ h = x := equalizer.lift_ι x (hfg x)
      use t
    have ⟨k, hk⟩ := hex (.mk (𝟙 a)) hs |>.mpr h₁
    dsimp [subset.ar, subset.dom] at k hk
    have : k ≫ h ≫ f = k ≫ h ≫ g := congr_arg (k ≫ ·) (equalizer.condition f g)
    rw [← assoc, ← assoc, hk, id_comp, id_comp] at this
    apply this
  intro hwp
  intro d f g
  constructor
  . -- only if part of the extensionality condition is straightforward and holds in any category.
    intro ⟨k, hfg⟩ x ⟨i, hi⟩
    use i ≫ k
    rw [assoc, hfg, hi]
  intro h
  suffices hc : subset.mk (f ⋒a(Ω) g) ≈ f by
    apply Sub_subset_iff_subs.mpr
    apply «§7.2».Corollary.«(1).1» ⟦f⟧ ⟦g⟧ (Ω := Ω) |>.mpr
    apply Sub_subset_iff_eqv.mp
    trans
    apply subset.iseqv.symm <| «§7.2».intersection.sub_out_eq_subset _ _
    apply hc
  have h₁ : subset.mk (f ⋒a(Ω) g) ⊆ f := by
    apply Sub_subset_iff_subs.mpr
    have := Sub_subset_iff_eqv.mp <| «§7.2».intersection.sub_out_eq_subset f g (Ω := Ω)
    rw [this]
    have : ⟦f⟧ ⊓ ⟦g⟧ ⊆ ⟦f⟧ := inf_le_left (a := (⟦f⟧ : Sub d)) (b := ⟦g⟧)
    apply this
  have h₂ : (χ (.mk (f ⋒a(Ω) g)) ⇒(Ω) χ f) = true' d := «§7.5».«Theorem 1».«(3)» Ω _ _ |>.mp h₁
  have h₃ := «CH.5».«§5.4».«Theorem 2» (Ω := Ω)
  apply «CH.4».«§4.2».Theorem _ _ (Ω := Ω) |>.mpr
  apply hwp.hom_ext (Ω := Ω)
  intro x
  have h₄ : x ≫ (χ (.mk (f ⋒a(Ω) g)) ⇒(Ω) χ f) = x ≫ true' d := congr_arg (x ≫ ·) h₂
  have h₅ : ((x ≫ χ (.mk (f ⋒a(Ω) g))) ⇒(Ω) x ≫ χ f) = true (Ω := Ω) := by
    rw [«CH.3».«§3.8».Excercises.«3», assoc, h₄, «CH.4».«§4.2».«Exercise 3», true', «CH.3».«§3.6».terminal_id, id_comp]
  match h₃ (x ≫ χ f) with
  | .inl ht =>
    have hf : x ∈ f := by
      have ⟨hPB, _⟩ := χ.spec f (Ω := Ω)
      let k := hPB.lift x (terminal.from _) (by rw [«CH.3».«§3.6».terminal_id, id_comp, ht])
      use k
      apply hPB.lift_fst x (terminal.from _) (by rw [«CH.3».«§3.6».terminal_id, id_comp, ht])
    have hg : x ∈ g := h x hf
    have hfgχ : x ≫ χ (.mk (f ⋒a(Ω) g)) = true (Ω := Ω) := by
      have hfg := «Theorem 1» Ω f g x |>.mpr ⟨hf, hg⟩
      apply «CH.4».«§4.8».«Exercise 2» _ _ |>.mp hfg
    rw [ht, hfgχ]
  | .inr hf =>
    match h₃ (x ≫ χ (.mk (f ⋒a(Ω) g))) with
    | .inl hfgt =>
      rw [hfgt, hf, «§7.6».«1.».imp_tf] at h₅
      have := «CH.5».«§5.4».«Exercise 4» h₅.symm
      contradiction
    | .inr hfgf =>
      rw [hfgf, hf]

abbrev «(a)» : Prop := ∀ {d : 𝓒} (f : subset d) (x : element d), x ∈ subset.mk (∸a(Ω) f) ↔ x ∉ f
abbrev «(b)» : Prop
  := ∀ {d : 𝓒} (f g : subset d) (x : element d), x ∈ subset.mk (f ⋓a(Ω) g) ↔ x ∈ f ∨ x ∈ g

open «CH.6».«§6.6» in
theorem «Theorem 3» : WellPointed 𝓒 ↔ «(a)» Ω := by
  symm
  constructor
  . contrapose
    intro hnwp ha
    -- TODO: bivalentではない場合にSub Ωで(a)が成り立たないことを示すが
    -- 方法がわからないのでいったんおいておく
    sorry
  . intro hwp
    have hbv := «CH.5».«§5.4».«Theorem 2» (Ω := Ω)
    intro d f x
    have h₁ : ∀ y : element Ω, y ≫ negT = true (Ω := Ω) ↔ y ≠ true := by
      intro y
      have ⟨hPB, _⟩ := χ.spec (.mk (false' (Ω := Ω))) (Ω := Ω)
      dsimp [subset.ar, subset.dom] at hPB
      rw [«CH.3».«§3.6».terminal_id] at hPB
      match hbv y with
      | .inl ht =>
        constructor
        . intro h ht
          have := χ.spec (.mk y) (Ω := Ω)
          dsimp [subset.ar, subset.dom] at this
          have ⟨hPB1, huniq⟩ := this
          have := huniq negT
          sorry
        intro h
        contradiction
      | .inr hf =>
        constructor
        . intro _ ht
          apply «CH.5».«§5.4».«Exercise 4» (Ω := Ω)
          rw [← hf, ← ht]
        intro _
        rw [hf, negT, hPB.w, id_comp]
    calc
      x ∈ subset.mk (∸a(Ω) f)
      _ ↔ x ≫ χ (.mk (∸a(Ω) f)) = true (Ω := Ω) := by apply «CH.4».«§4.8».«Exercise 2»
      _ ↔ x ≫ χ f ≫ negT = true (Ω := Ω) := by rw [«§7.1».complement.eq]
      _ ↔ x ≫ χ f ≠ true := by rw [← assoc, h₁ (x ≫ χ f)]
      _ ↔ x ∉ f := «CH.4».«§4.8».«Exercise 2» _ _ |>.not.symm

abbrev «(c)» : Prop
  := ∀ (y z : element Ω), (y ∪(Ω) z) = true (Ω := Ω) ↔ y = true (Ω := Ω) ∨ z = true (Ω := Ω)

theorem «Theorem 4» : «(b)» Ω ↔ «(c)» Ω := by
  constructor
  . intro hb y z
    let f := rf.f y
    let g := rf.f z
    let x : ⊤_ 𝓒 ⟶ ⊤_ 𝓒 := 𝟙 _
    calc
      (y ∪(Ω) z) = true (Ω := Ω)
      _ ↔ x ≫ (y ∪(Ω) z) = true (Ω := Ω) := by rw [id_comp]
      _ ↔ x ≫ χ (.mk (.mk f ⋓a(Ω) .mk g)) = true (Ω := Ω) := by simp only [← rf.subset_f.eq]
      _ ↔ x ∈ subset.mk (.mk f ⋓a(Ω) .mk g) := by symm; apply «CH.4».«§4.8».«Exercise 2»
      _ ↔ x ∈ subset.mk f ∨ x ∈ subset.mk g := hb _ _ _
      _ ↔ x ≫ χ (.mk f) = true (Ω := Ω) ∨ x ≫ χ (.mk g) = true (Ω := Ω) := by simp only [«CH.4».«§4.8».«Exercise 2» (Ω := Ω)]
      _ ↔ y = true (Ω := Ω) ∨ z = true (Ω := Ω) := by rw [id_comp, id_comp]; simp only [← rf.subset_f.eq]
  intro hc d f g x
  calc
    x ∈ subset.mk (f ⋓a(Ω) g)
    _ ↔ x ≫ χ (.mk (f ⋓a(Ω) g)) = true (Ω := Ω) := by apply «CH.4».«§4.8».«Exercise 2»
    _ ↔ x ≫ (χ f ∪(Ω) χ g) = true (Ω := Ω) := by rw [«§7.1».union.eq]
    _ ↔ ((x ≫ χ f) ∪(Ω) (x ≫ χ g)) = true (Ω := Ω) := by rw [«CH.3».«§3.8».Excercises.«3», assoc]
    _ ↔ x ≫ χ f = true (Ω := Ω) ∨ x ≫ χ g = true (Ω := Ω) := hc _ _
    _ ↔ x ∈ f ∨ x ∈ g := by simp only [«CH.4».«§4.8».«Exercise 2» (Ω := Ω)]

variable (𝓒)
abbrev disjunctive : Prop := «(c)» Ω
variable {𝓒}

theorem «bivalent only if disjunctive» [WellPointed 𝓒] : disjunctive 𝓒 Ω := by
  -- TODO: obviouslyらしいがうまく証明できない
  have hbv := «CH.5».«§5.4».«Theorem 2» (Ω := Ω)
  intro y z
  let yz := y ∪(Ω) z
  constructor
  . intro hyz
    match hbv y, hbv z with
    | .inr hyf, .inr hzf =>
      left
      rw [hyf]
      symm
      have := «CH.5».«§5.4».«Exercise 4» (Ω := Ω)
      sorry
    | .inl hyt, _ => left; exact hyt
    | _, .inl hzt => right; exact hzt
  intro hyz
  match hyz with
  | .inl ht =>
    match hbv z with
    | .inl hzt =>
      rw [ht, hzt]
      apply «§7.6».«1.».Exercise.or_tt
    | .inr hzf =>
      rw [ht, hzf]
      apply «§7.6».«1.».Exercise.or_tf
  | .inr ht =>
    match hbv y with
    | .inl hyt =>
      rw [hyt, ht]
      apply «§7.6».«1.».Exercise.or_tt
    | .inr hzf =>
      rw [ht, hzf]
      apply «§7.6».«1.».Exercise.or_ft

-- TODO: bivalentを示す問題だがbivalentに入れていたnonDegenerateの条件を入れられない
-- bivalentの定義を見直した方が良いかも
open «§7.3» in
theorem «Theorem 5» : Nonempty (Boolean 𝓒 Ω) ∧ nonDegenerate 𝓒 → (disjunctive 𝓒 Ω ↔ WellPointed 𝓒) := by
  intro ⟨hbl, hnd⟩
  symm
  constructor
  . intro h
    apply «bivalent only if disjunctive»
  intro hdis
  have hbl := Classical.choice hbl
  have hb := «Theorem 4» Ω |>.mpr hdis (d := Ω)
  have hbv : bivalent 𝓒 hnd (Ω := Ω) := by
    intro f
    have h₁ : subset.mk (.mk f ⋓a(Ω) .mk (∸a(Ω) .mk f)) ≈ .mk (𝟙 _) := by
      trans
      apply «§7.1».union.ext Ω (subset.mk f).mk_out.symm («§7.1».complement.ext Ω (subset.mk f).mk_out.symm)
      trans
      apply «§7.1».union.sub_out_eq_subset
      apply «CH.4».«§4.1».Sub_subset_iff_eqv.mpr
      apply «§7.3».«Theorem 1».em
      apply «§7.3».«Theorem 1».«(6)→(7)»
      apply «§7.3».«Theorem 1».«(5)→(6)»
      apply «§7.3».«Theorem 1».«(4)→(5)»
      apply «§7.3».«Theorem 1».«(3)→(4)»
      apply «§7.3».«Theorem 1».«(2)→(3)»
      apply «§7.3».«Theorem 1».«(1)→(2)»
      apply hbl
    have h₂ : ∀ (x : element Ω), x ∈ subset.mk f ∨ x ∈ subset.mk (∸a(Ω) .mk f) := by
      intro x
      apply hb (.mk f) (.mk (∸a(Ω) .mk f)) x |>.mp
      apply «CH.4».«§4.8».«Exercise 2» _ _ (Ω := Ω) |>.mpr
      rw [
        «CH.4».«§4.2».Theorem _ _ (Ω := Ω) |>.mp h₁, «CH.4».«§4.2».«Exercise 2''»,
        true', ← assoc, terminal.comp_from, «CH.3».«§3.6».terminal_id, id_comp]
    have h₃ : ∀ (x : element Ω), ¬ (x ∈ subset.mk f ∧ x ∈ subset.mk (∸a(Ω) .mk f)) := by
      intro x hfnf
      have h₁ := «Theorem 1» Ω (.mk f) _ x |>.mpr hfnf
      have ⟨k, hk⟩ : x ∈ subset.mk (initial.to Ω) := by
        have ⟨h₃, _⟩ := «§7.2».«Theorem 3» (.mk f) (Ω := Ω)
        apply «CH.4».«§4.8».«Exercise 1» _ _ h₃ x h₁
      dsimp [subset.dom] at k
      have h₃ := «CH.3».«§3.16».«Theorem 1».«(2)» k
      have h₄ : initial.to _ = h₃.inv := by ext
      apply hnd
      rw [h₄]
      apply h₃.isIso_inv
    sorry
  sorry

abbrev h' {a b d : 𝓒} (f : a ⟶ d) (g : b ⟶ d) (hf : Mono f) (hg : Mono g) : (.mk f ⋒o(Ω) .mk g) ⟶ b
  := «CH.7».«§7.1».«Theorem 2'» Ω f g |>.choose

theorem «Exercise» [WellPointed 𝓒] (f g : subset d) (h : ∀ x : element d, x ∈ f → x ∈ g)
    : IsIso (h' Ω g.ar f.ar g.mono f.mono) := by
  have := f.mono
  have := g.mono
  have hs := «CH.7».«§7.1».«Theorem 2'» Ω g.ar f.ar |>.choose
  have ⟨q, hp, hpmono, hqmono, hPB⟩ := @«CH.7».«§7.1».«Theorem 2'» _ _ _ _ _ Ω _ g.ar f.ar g.mono f.mono |>.choose_spec
  apply «CH.5».«§5.1».Corollary _ Ω |>.mpr
  constructor
  . apply «CH.5».«§5.5».«Theorem 1».«(i)» _ (Ω := Ω) |>.mp
    intro y
    sorry
  apply «CH.5».«§5.5».«Theorem 1».«(ii)» _ (Ω := Ω) |>.mp
  sorry
