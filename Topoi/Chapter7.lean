import Topoi.Chapter6

open CategoryTheory Category Limits

noncomputable section

open «CH.4».«§4.2» «CH.4».«§4.3»

variable {𝓒 : Type*} [Category 𝓒]

namespace «CH.7»
-- Algebra of subobjects

namespace «§7.1»
-- Complement, intersection, union

variable (Ω : 𝓒) [ElementaryTopos Ω]

section

variable {d : 𝓒} (χ : d ⟶ Ω)
abbrev s : 𝓒 := Ω_axiom' χ |>.choose
abbrev rf : s Ω χ ⟶ d := Ω_axiom' χ |>.choose_spec.choose
omit [ElementaryTopos Ω] in
lemma rf.spec : Mono (rf Ω χ) ∧ IsPullback (rf Ω χ) (terminal.from (s Ω χ)) χ true
  := Ω_axiom' χ |>.choose_spec.choose_spec.1
omit [ElementaryTopos Ω] in
lemma rf.uniq : ∀ y : s Ω χ ⟶ d, Mono y ∧ IsPullback y (terminal.from (s Ω χ)) χ true → y = rf Ω χ
  := Ω_axiom' χ |>.choose_spec.choose_spec.2

lemma rf.mono {Ω d : 𝓒} [ElementaryTopos Ω] {χ : d ⟶ Ω}: Mono (rf Ω χ) := by
  apply «§7.1».rf.spec Ω _ |>.1

end

lemma χ_rf_eq {a : 𝓒} (χ' : a ⟶ Ω) : χ (rf Ω χ') (by apply rf.mono) = χ' := by
  symm
  apply χ.spec (rf Ω χ') (by apply rf.mono) (Ω := Ω) |>.2
  apply rf.spec Ω χ' |>.2

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

abbrev complement {a d : 𝓒} (f : a ⟶ d) (hf : Mono f)
  := rf Ω <| χ f hf (Ω := Ω) ≫ «CH.6».«§6.6».negT
-- notation "-'" Ω f hf => complement Ω f hf

abbrev intersection {a b d : 𝓒} (f : a ⟶ d) (hf : Mono f) (g : b ⟶ d) (hg : Mono g)
  := rf Ω <| χ f hf ∩(Ω) χ g hg
-- notation f "⟦" hf "⟧∩(" Ω ")'" g "⟦" hg "⟧" => intersection Ω f hf g hg

abbrev union {a b d : 𝓒} (f : a ⟶ d) (hf : Mono f) (g : b ⟶ d) (hg : Mono g)
  := rf Ω <| χ f hf ∪(Ω) χ g hg
-- notation f "⟦" hf "⟧∪(" Ω ")'" g "⟦" hg "⟧" => union Ω f hf g hg

open «CH.6».«§6.7» in
theorem «Theorem 2» {a b c d : 𝓒}
  (f : a ⟶ d) (hf : Mono f) (g : b ⟶ d) (hg : Mono g)
  (f' : c ⟶ b) (hf' : Mono f') (g' : c ⟶ a) (_hg' : Mono g')
  (hPB : IsPullback f' g' g f)
  : χ (f' ≫ g) (by apply mono_comp) (Ω := Ω) = χ (intersection Ω f hf g hg) (by apply rf.mono) := by
  set α := f' ≫ g with hα
  set χf := χ f hf (Ω := Ω)
  set χg := χ g hg (Ω := Ω)
  set trtr := (prod.lift (TRUE Ω) (TRUE Ω)) with htrtr
  -- NOTE: 教科書に証明無し
  have hPB1 : IsPullback α (terminal.from c) (prod.lift χf χg) trtr := by
    have ⟨hχf, _⟩ := χ.spec f hf (Ω := Ω)
    have ⟨hχg, _⟩ := χ.spec g hg (Ω := Ω)
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
    apply χ.spec trtr («CH.3».«§3.6».Excercises.«3» _ _) (Ω := Ω) |>.1
  have hPB3 := hPB1.paste_vert hPB2
  rw [comp_id] at hPB3
  have ⟨_, huniq⟩ := χ.spec α (by apply mono_comp) (Ω := Ω)
  have := huniq (prod.lift χf χg ≫ «CH.6».«§6.6».conT) hPB3 |>.symm
  rw [this, χ_rf_eq]

-- Theorem 2の後半内容
lemma subs_equiv_pullback {a b d c c' : 𝓒}
  {f : a ⟶ d} {g : b ⟶ d} {f' : c ⟶ b} {g' : c ⟶ a}
  [Mono f] [Mono g] [Mono f'] [Mono g']
  {α : c' ⟶ d} [Mono α]
  (h : f' ≫ g ≃ₛ α) (hPB : IsPullback f' g' g f)
  : ∃ (p : c' ⟶ b) (q : c' ⟶ a), Mono p ∧ Mono q ∧ IsPullback p q g f := by
  have ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := h
  let p : c' ⟶ b := j ≫ f'
  let q : c' ⟶ a := j ≫ g'
  have ⟨iiso, jiso⟩ := «CH.4».«§4.1».equiv_iso hi hj
  use p, q
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

abbrev intrsct {a b d : 𝓒} (Ω : 𝓒) (f : a ⟶ d) (hf : Mono f) (g : b ⟶ d) (hg : Mono g)
  := «§7.1».s Ω <| χ f hf ∩(Ω) χ g hg

lemma «Theorem 2'» {a b d : 𝓒} (Ω : 𝓒) [ElementaryTopos Ω] (f : a ⟶ d) (g : b ⟶ d) [Mono f] [Mono g]
  : ∃ (p : intrsct Ω f ‹Mono f› g ‹Mono g› ⟶ b) (q : intrsct Ω f ‹Mono f› g ‹Mono g› ⟶ a),
  Mono p ∧ Mono q ∧ IsPullback p q g f := by
  let f' := pullback.snd f g
  let g' := pullback.fst f g
  have ⟨hPB, hf', hg'⟩ := getPullbackCone Ω ‹Mono f› ‹Mono g›
  have := «§7.1».«Theorem 2» Ω f ‹Mono f› g ‹Mono g› f' hf' g' hg' hPB
  have := «CH.4».«§4.2».Theorem _ _ _ _ |>.mpr this
  have hMono : Mono («§7.1».intersection Ω f ‹Mono f› g ‹Mono g›) := by
    apply rf.mono
  apply «§7.1».subs_equiv_pullback this hPB

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
  have hf'Epi : Epi f' := «CH.5».«§5.3».«Fact 1» hPBleft.flip <| epiFstar Ω g
  have ⟨k, hkw, hkuniq⟩ := epiMonoUniversal Ω f f' i hf'Epi hiMono hf'fst
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
  : χ (im Ω (coprod.desc f g)) (monoImage Ω _) (Ω := Ω) = χ (union Ω f hf g hg) (by apply rf.spec Ω _ |>.1) := by
  have ⟨hχf, _⟩ := χ.spec f hf (Ω := Ω)
  have ⟨hχg, _⟩ := χ.spec g hg (Ω := Ω)
  let χf := χ f hf (Ω := Ω)
  let χg := χ g hg (Ω := Ω)
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
  have hPB5 : IsPullback i (terminal.from _) «CH.6».«§6.6».disT (TRUE Ω) := (χ.spec i <| monoImage Ω _) |>.1
  have hPB := hPB4.paste_vert hPB5
  rw [terminal.comp_from] at hPB
  have ⟨_, huniq⟩ := χ.spec α (monoImage Ω _) (Ω := Ω)
  have := huniq (prod.lift χf χg ≫ «CH.6».«§6.6».disT) hPB |>.symm
  rw [this, χ_rf_eq]

end «§7.1»

namespace «§7.2»
-- Sub(d) as a latttice

open «CH.4».«§4.1»

variable {d : 𝓒}

open «CH.5».«§5.2» in
instance «Theorem 1» (Ω : 𝓒) {h : ElementaryTopos Ω} : Lattice (Subs d) where
  le := subobject' (d := d)
  le_refl f := Subs.eqv.refl f |>.1
  le_trans f g h := by
    intro ⟨i, hfg⟩ ⟨j, hgh⟩
    use i ≫ j
    rw [assoc, hgh, hfg]
  lt_iff_le_not_le f g := by
    tauto
  le_antisymm := by
    intro ⟨a, f, hf⟩ ⟨b, g, hg⟩ ⟨i, hi⟩ ⟨j, hj⟩
    dsimp at i hi j hj
    -- NOTE: この定義はできないはず
    sorry
  -- (1)
  -- 教科書曰くrelafive easy to see
  inf := λ ⟨a, f, hf⟩ ⟨b, g, hg⟩ ↦
    ⟨_, «§7.1».intersection Ω f hf g hg, by apply «§7.1».rf.mono⟩
  inf_le_left := by
    intro ⟨a, f, hf⟩ ⟨b, g, hg⟩
    let f' := pullback.snd f g
    let g' := pullback.fst f g
    have ⟨hPB, hf', hg'⟩ := «§7.1».getPullbackCone Ω hf hg
    have := «§7.1».«Theorem 2» Ω _ hf _ hg _ hf' _ hg' hPB
    have ⟨⟨i, h₁⟩, ⟨j, h₂⟩⟩ := «CH.4».«§4.2».Theorem
      (f' ≫ g) (by apply mono_comp)
      («§7.1».intersection Ω f hf g hg) (by apply «§7.1».rf.mono) |>.mpr this
    use j ≫ g'
    dsimp
    rw [assoc, ← hPB.w, h₂]
  inf_le_right := by
    intro ⟨a, f, hf⟩ ⟨b, g, hg⟩
    let f' := pullback.snd f g
    let g' := pullback.fst f g
    have ⟨hPB, hf', hg'⟩ := «§7.1».getPullbackCone Ω hf hg
    have := «§7.1».«Theorem 2» Ω _ hf _ hg _ hf' _ hg' hPB
    have ⟨⟨i, h₁⟩, ⟨j, h₂⟩⟩ := «CH.4».«§4.2».Theorem
      (f' ≫ g) (by apply mono_comp)
      («§7.1».intersection Ω f hf g hg) (by apply «§7.1».rf.mono) |>.mpr this
    use j ≫ f'
    dsimp
    rw [assoc, h₂]
  le_inf := by
    intro ⟨c, h, hh⟩ ⟨a, f, hf⟩ ⟨b, g, hg⟩ ⟨i, hfh⟩ ⟨j, hgh⟩
    dsimp at i hfh j hgh
    dsimp
    let f' := pullback.snd f g
    let g' := pullback.fst f g
    have ⟨hPB, hf', hg'⟩ := «§7.1».getPullbackCone Ω hf hg
    have := «§7.1».«Theorem 2» Ω _ hf _ hg _ hf' _ hg' hPB
    have ⟨⟨i₁, h₁⟩, ⟨i₂, h₂⟩⟩ := «CH.4».«§4.2».Theorem
      (f' ≫ g) (by apply mono_comp)
      («§7.1».intersection Ω f hf g hg) (by apply «§7.1».rf.mono) |>.mpr this
    have w : i ≫ f = j ≫ g :=by rw [hfh, hgh]
    use pullback.lift i j w ≫ i₁
    dsimp
    rw [assoc, h₁, ← assoc, pullback.lift_snd i j w, hgh]
  -- (2)
  sup := λ ⟨a, f, hf⟩ ⟨b, g, hg⟩ ↦
    ⟨_, «§7.1».union Ω f hf g hg, by apply «§7.1».rf.mono⟩
  le_sup_left := by
    intro ⟨a, f, hf⟩ ⟨b, g, hg⟩
    dsimp
    let i₁ : a ⟶ a ⨿ b := coprod.inl
    have := «§7.1».«Theorem 3» Ω _ hf _ hg
    have ⟨⟨i, h₁⟩, ⟨j, h₂⟩⟩ := «CH.4».«§4.2».Theorem
      (im Ω (coprod.desc f g)) (monoImage Ω _)
      («§7.1».union Ω f hf g hg) (by apply «§7.1».rf.mono) |>.mpr this
    use i₁ ≫ (fstar' Ω <| coprod.desc f g) ≫ i
    dsimp
    rw [assoc, assoc, h₁, epiMonoFactor, coprod.inl_desc]
  le_sup_right := by
    intro ⟨a, f, hf⟩ ⟨b, g, hg⟩
    dsimp
    let i₂ : b ⟶ a ⨿ b := coprod.inr
    have := «§7.1».«Theorem 3» Ω _ hf _ hg
    have ⟨⟨i, h₁⟩, ⟨j, h₂⟩⟩ := «CH.4».«§4.2».Theorem
      (im Ω (coprod.desc f g)) (monoImage Ω _)
      («§7.1».union Ω f hf g hg) (by apply «§7.1».rf.mono) |>.mpr this
    use i₂ ≫ (fstar' Ω <| coprod.desc f g) ≫ i
    dsimp
    rw [assoc, assoc, h₁, epiMonoFactor, coprod.inr_desc]
  sup_le := by
    intro ⟨a, f, hf⟩ ⟨b, g, hg⟩ ⟨c, h, hh⟩ ⟨ha, hfh⟩ ⟨hb, hgh⟩
    dsimp at ha hfh hb hgh
    dsimp
    have : coprod.desc f g = coprod.desc ha hb ≫ h := by
      rw [← hfh, ← hgh, coprod.desc_comp]
    let e : 𝓒 := fa' Ω <| coprod.desc ha hb
    let j : a ⨿ b ⟶ e := fstar' Ω <| coprod.desc ha hb
    let k : e ⟶ c := im Ω <| coprod.desc ha hb
    have jepi : Epi j := epiFstar Ω <| coprod.desc ha hb
    have khMono : Mono (k ≫ h) := by
      have : Mono k := monoImage Ω <| coprod.desc ha hb
      apply mono_comp
    have : j ≫ k ≫ h = coprod.desc f g := by
      rw [← assoc, epiMonoFactor, this]
    have ⟨u, ⟨⟨_, hu, _⟩, _⟩⟩ := epiMonoUniversal Ω (coprod.desc f g) j (k ≫ h) jepi khMono this

    have := «§7.1».«Theorem 3» Ω _ hf _ hg
    have ⟨⟨i₁, h₁⟩, ⟨i₂, h₂⟩⟩ := «CH.4».«§4.2».Theorem
      (im Ω (coprod.desc f g)) (monoImage Ω _)
      («§7.1».union Ω f hf g hg) (by apply «§7.1».rf.mono) |>.mpr this
    use i₂ ≫ u ≫ k
    dsimp
    rw [assoc, assoc, hu, h₂]

namespace «Corollary»

variable {Ω : 𝓒} [ElementaryTopos Ω]

variable {a b : 𝓒} {f : a ⟶ d} {g : b ⟶ d} {hf : Mono f} {hg : Mono g}

theorem «(1).1» : (⟨_, f, hf⟩ : Subs d) ⊆ₛ' ⟨_, g, hg⟩ ↔ «§7.1».intersection Ω f hf g hg ≃ₛ f := by
  set inf : Subs d := ⟨_, «§7.1».intersection Ω f hf g hg, by apply «§7.1».rf.mono⟩
  let f' : Subs d := ⟨_, f, hf⟩
  let g' : Subs d := ⟨_, g, hg⟩
  -- 教科書ではLatticeの定義からすぐに導かれるとしているが、その場合 inf = f' になってしまうので使えない
  -- と思ったけどSubs dがskeletalなことを使えばよかった……？
  constructor
  . intro h₂
    constructor
    . apply «Theorem 1» Ω (d := d) (h := inferInstance) |>.inf_le_left f' g'
    have h₁ : f' ⊆ₛ' f' := «Theorem 1» Ω (d := d) (h := inferInstance) |>.le_refl _
    apply «Theorem 1» Ω (d := d) (h := inferInstance) |>.le_inf f' f' g' h₁ h₂
  intro ⟨_, h₁⟩
  have h₂ : inf ⊆ₛ' g' := «Theorem 1» Ω (d := d) (h := inferInstance) |>.inf_le_right f' g'
  apply «Theorem 1» Ω (d := d) (h := inferInstance) |>.le_trans f' inf g' h₁ h₂

theorem «(1).2» : (⟨_, f, hf⟩ : Subs d) ⊆ₛ' ⟨_, g, hg⟩ ↔ «§7.1».union Ω f hf g hg ≃ₛ g := by
  set sup : Subs d := ⟨_, «§7.1».union Ω f hf g hg, by apply «§7.1».rf.mono⟩
  let f' : Subs d := ⟨_, f, hf⟩
  let g' : Subs d := ⟨_, g, hg⟩
  constructor
  . intro h₁
    constructor
    . have h₂ : g' ⊆ₛ' g' := «Theorem 1» Ω (d := d) (h := inferInstance) |>.le_refl _
      apply «Theorem 1» Ω (d := d) (h := inferInstance) |>.sup_le f' g' g' h₁ h₂
    apply «Theorem 1» Ω (d := d) (h := inferInstance) |>.le_sup_right f' g'
  intro ⟨h₂, _⟩
  have h₁ : f' ⊆ₛ' sup := «Theorem 1» Ω (d := d) (h := inferInstance) |>.le_sup_left f' g'
  apply «Theorem 1» Ω (d := d) (h := inferInstance) |>.le_trans f' sup g' h₁ h₂

open «CH.6».«§6.6»

theorem «(2)» : (⟨_, f, hf⟩ : Subs d) ⊆ₛ' ⟨_, g, hg⟩
    ↔ ∃! h : d ⟶ ImpT (Ω := Ω), (prod.lift (χ f hf) (χ g hg)) = h ≫ e := by
  trans
  apply «(1).1» (hf := hf) (hg := hg) (Ω := Ω)
  let χfandg : d ⟶ Ω ⨯ Ω := prod.lift (χ f hf) (χ g hg)
  trans
  apply «CH.4».«§4.2».Theorem (Ω := Ω) _ (by apply «§7.1».rf.mono) _ hf
  rw [«§7.1».χ_rf_eq]
  have : χfandg ≫ (prod.fst : Ω ⨯ Ω ⟶ Ω) = χ f hf :=by
    rw [prod.lift_fst]
  nth_rewrite 2 [← this]
  constructor
  . intro h
    have ⟨l, ⟨hl, huniq⟩⟩ := equalizer.existsUnique χfandg h
    use l
    dsimp
    constructor
    . rw [hl]
    intro y hy
    apply huniq y hy.symm
  intro ⟨h, hu, huniq⟩
  dsimp at hu
  dsimp [χfandg]
  rw [hu, assoc, assoc, equalizer.condition]

end «Corollary»

instance : LE (Subs d) := ⟨(· ⊆ₛ' ·)⟩

instance «Theorem 2» : BoundedOrder (Subs d) where
  top := ⟨d, 𝟙 d, by apply id_mono⟩
  le_top := by
    intro ⟨_, f, hf⟩
    use f
    dsimp
    rw [comp_id]
  bot := ⟨⊥_ 𝓒, initial.to d, by apply «CH.3».«§3.16».«Theorem 1».«(4)»⟩
  bot_le := by
    intro ⟨_, f, hf⟩
    use initial.to _
    dsimp
    rw [initial.to_comp]

theorem «Exercise 1» {a : 𝓒} (f : a ⟶ d) (hf : Mono f) : f ≃ₛ 𝟙 d ↔ IsIso f := by
  constructor
  . intro ⟨⟨i, h1⟩, ⟨j, h2⟩⟩
    constructor
    use j
    constructor
    . apply hf.right_cancellation
      rw [assoc, h2, id_comp, comp_id]
    apply h2
  intro h
  constructor
  . use f
    rw [comp_id]
  use inv f
  simp

-- distributed latticeの証明は§8.3にて

open «CH.6».«§6.6» in
theorem «Theorem 3» {a Ω : 𝓒} [ElementaryTopos Ω] (f : a ⟶ d) (hf : Mono f) :
    «§7.1».intersection Ω f hf («§7.1».complement Ω f hf) (by apply «§7.1».rf.mono) ≃ₛ initial.to _ := by
  let χf := χ f hf (Ω := Ω)
  let na : 𝓒 := «§7.1».s Ω <| χf ≫ negT
  let nf : na ⟶ d := «§7.1».complement Ω f hf
  have ⟨hPB1, hPB1uniq⟩ := χ.spec («CH.5».«§5.4».false' (Ω := Ω)) («CH.6».«§6.6».element.mono _) (Ω := Ω)
  have ⟨hnfMono, hPB2⟩ := «§7.1».rf.spec Ω <| χf ≫ negT
  let h : na ⟶ ⊤_ 𝓒 := hPB1.lift (nf ≫ χf) (terminal.from na) (by
    have := hPB2.w
    dsimp [negT] at this
    rw [assoc, this])
  have p : nf ≫ χf = terminal.from na ≫ «CH.5».«§5.4».false' := by
    dsimp [nf, «§7.1».complement, negT]

    sorry
  have : terminal.from na = terminal.from na ≫ 𝟙 _ := by rw [comp_id]
  rw [this] at hPB2
  rw [«CH.3».«§3.6».terminal_id] at hPB1
  have hPB3 := hPB2.of_bot p hPB1
  have ⟨hPB, hf', hnf'⟩ := «§7.1».getPullbackCone Ω hf (g := nf) (by apply «§7.1».rf.mono)
  let c : 𝓒 := pullback f nf
  let g : c ⟶ a := pullback.fst f nf
  have h₁ : g ≫ f ≫ χf = terminal.from _ ≫ «CH.5».«§5.4».false' := by
    rw [← assoc, ← hPB.w, assoc, p, ← assoc, terminal.comp_from]
  have h₂ : g ≫ f ≫ χf = (g ≫ terminal.from _) ≫ true := by
    have := χ.spec f hf (Ω := Ω) |>.1.w
    rw [this, assoc]
  have ⟨hPB', huniq⟩ := χ.spec (initial.to (⊤_ 𝓒)) («CH.3».«§3.16».«Theorem 1».«(4)» _) (Ω := Ω)
  let k : c ⟶ ⊥_ 𝓒 := hPB'.lift (terminal.from _) (g ≫ terminal.from _) (by rw [← h₁, ← h₂])
  have hcz : c ≅ (⊥_ 𝓒) := «CH.3».«§3.16».«Theorem 1».«(2)» k
  sorry

lemma «§3.6.ex3» {a : 𝓒} (f : ⊤_ 𝓒 ⟶ a) : Mono f := «CH.3».«§3.6».Excercises.«3» 𝓒 f

theorem «Theorem 4» {Ω : 𝓒} [ElementaryTopos Ω] : «CH.5».«§5.4».false' ≃ₛ «§7.1».complement Ω true («§3.6.ex3» _ ) (d := Ω) := by
  have := «CH.4».«§4.2».Theorem (Ω := Ω)
    («CH.5».«§5.4».false' (Ω := Ω)) («CH.6».«§6.6».element.mono _)
    («§7.1».complement Ω true («§3.6.ex3» _)) (by apply «§7.1».rf.mono) |>.mpr
  apply this
  rw [«§7.1».χ_rf_eq, «CH.4».«§4.2».«Exercise 1», id_comp]
  dsimp [«CH.6».«§6.6».negT]

lemma «§3.16.th1.(4)» {a : 𝓒} (f : ⊥_ 𝓒 ⟶ a) : Mono f := «CH.3».«§3.16».«Theorem 1».«(4)» _

open «CH.5».«§5.4» in
theorem «Theorem 5» {Ω : 𝓒} [ElementaryTopos Ω]
    (hf : ∃ f: Subs Ω, f = ⟨_, «§7.1».complement Ω true («§3.6.ex3» _), by apply «§7.1».rf.mono⟩)
  : hf.choose = ⟨_, «CH.5».«§5.4».false', «§3.6.ex3» _⟩ := by
  have ⟨⟨a, f, hf⟩, hcomp⟩ := hf
  let z := «§7.1».s Ω f
  let j := «§7.1».rf Ω f
  have : «§7.1».intersection Ω true («§3.6.ex3» _) f hf  ≃ₛ initial.to _ := by
    -- apply «Theorem 3» (true (Ω := Ω)) («§3.6.ex3» _) (Ω := Ω)
    sorry
  have ⟨p, q, hp, hq, hPB⟩ := «§7.1».«Theorem 2'» Ω true f
  have h1 : «§7.1».intersection Ω true («§3.6.ex3» _) f hf = p ≫ f := by
    symm
    apply «§7.1».rf.uniq
    constructor
    . apply mono_comp
    sorry
  have hPB : IsPullback (initial.to a) (terminal.from (⊥_ 𝓒)) f true := by
    rw [h1] at this
    have hini : Mono (initial.to Ω) := «§3.16.th1.(4)» _
    have ⟨p, q, _, _, hPB2⟩ := «§7.1».subs_equiv_pullback this hPB
    have hp : initial.to _ = p := by ext
    have hq : terminal.from _ = q := by ext
    rw [hp, hq]
    apply hPB2
  have := χ.spec (initial.to a) («§3.16.th1.(4)» _) (Ω := Ω) |>.2 f hPB
  have h2 : f = terminal.from a ≫ false' := by
    apply this.trans <| «CH.5».«§5.4».«Exercise 3» a (Ω := Ω)
  have hf1 : f ⊆ₛ false' := ⟨terminal.from a, h2.symm⟩
  -- これ以下の証明はSubsのLattice, DistributedLatticeの定義から導くが、うまいことできなさそうなのでいったんおいておく
  -- hf1 から ⊤ ∪ f ⊆ ⊤ ∪ ⊥がLatticeの定義から導かれる
  -- ⊤ ∪ f は f が ⊤のcomplementなので ⊤ ∪ f ≃ 𝟙 Ωになる
  -- 𝟙 Ω は Subsの上限なので⊤ ∪ ⊥ ≃ 𝟙 Ω ... 1
  -- 定理3からf ∩ -f ≃ 0、定理4から⊥ ≃ -⊤のため⊤ ∩ -⊤ = ⊤ ∩ ⊥ ≃ 0 ... 2
  -- 1と2から⊥もcomplementで、DistributedLatticeではcomplementは一意なのでf ≃ ⊥
  sorry

end «§7.2»

namespace «§7.3»
-- Boolean topoi

open «CH.4».«§4.1»

abbrev Boolean (𝓒 : Type*) [Category 𝓒] (Ω : 𝓒) [ElementaryTopos Ω]
  := ∀ d : 𝓒, BooleanAlgebra (Subs d)

namespace «Theorem 1»
variable (Ω : 𝓒) [ElementaryTopos Ω]

def «(1)→(2)» : Boolean 𝓒 Ω → BooleanAlgebra (Subs Ω) := by
  intro h
  apply h Ω

def «(2)→(3)» : BooleanAlgebra (Subs Ω) → ∃ f: Subs Ω, f = ⟨_, «§7.1».complement Ω true («§3.6.ex3» _), by apply «§7.1».rf.mono⟩ := by
  intro h

  sorry


-- instance (Ω : 𝓒) {h : ElementaryTopos Ω} {d : 𝓒}: DistribLattice (Subs d) where
--   le := (· ⊆ₛ' ·)
--   le_refl := sorry
--   le_trans := sorry
--   lt_iff_le_not_le := sorry
--   le_antisymm := sorry
--   sup := λ ⟨a, f, hf⟩ ⟨b, g, hg⟩ ↦
--     ⟨_, «§7.1».union Ω f hf g hg, by apply «§7.1».rf.mono⟩
--   le_sup_left := sorry
--   le_sup_right := sorry
--   sup_le := sorry
--   inf := sorry
--   inf_le_left := sorry
--   inf_le_right := sorry
--   le_inf := sorry
--   le_sup_inf := sorry
