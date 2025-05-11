import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

open CategoryTheory Category CategoryTheory.Limits

noncomputable section

namespace CategoryTheory.Limits

variable {J : Type u₁} [Category.{v₁} J]
variable {C : Type u₃} [Category.{v₃} C]

variable [HasBinaryProducts C]

structure PCone (F : J ⥤ C) (a : C) where
  pt : C
  -- a ⨯ pt ⟶ F.obj j
  π : (Functor.const J).obj pt ⋙ prod.functor.obj a ⟶ F


variable {F : J ⥤ C} {a : C}

theorem PCone.w (c : PCone F a) {j j' : J} (f : j ⟶ j') :
    c.π.app j ≫ F.map f = c.π.app j' := by
  rw [← c.π.naturality f]
  dsimp
  rw [prod.map_id_id, id_comp]

structure PConeMorphism (A B : PCone F a) where
  hom : A.pt ⟶ B.pt
  w : ∀ j, prod.map (𝟙 _) hom ≫ B.π.app j = A.π.app j := by aesop_cat

instance PCone.category (F : J ⥤ C) (a : C) : Category (PCone F a) where
  Hom c c' := PConeMorphism c c'
  id c := {hom := 𝟙 _}
  comp f g := {
    hom := f.hom ≫ g.hom
    w j := by
      have hf := f.w j
      have hg := g.w j
      rw [prod.map_id_comp, assoc, hg, hf]
  }

@[ext]
theorem PConeMorphism.ext {c c' : PCone F a} (f g : PConeMorphism c c') (h : f.hom = g.hom) :
    f = g := by
  cases f
  cases g
  congr

theorem PConeMorphism.comp (A B C : PCone F a) (f : A ⟶ B) (g : B ⟶ C) :
  f ≫ g = {hom := f.hom ≫ g.hom, w j := by rw [prod.map_id_comp, assoc, g.w j, f.w j]} := by
    rfl

def PCone.ext {c c' : PCone F a} (e : c.pt ≅ c'.pt)
    (h : ∀ j, c.π.app j = prod.map (𝟙 _) e.hom ≫ c'.π.app j := by aesop_cat) : c ≅ c' where
      hom := {
        hom := e.hom
        w j := by
          exact (h j).symm
      }
      inv := {
        hom := e.inv
        w j := by
          rw [h j, ← assoc, ← prod.map_id_comp, e.inv_hom_id, prod.map_id_id, id_comp]
      }
      hom_inv_id := by
        apply PConeMorphism.ext
        rw [PConeMorphism.comp]
        dsimp
        rw [e.hom_inv_id]
        rfl
      inv_hom_id := by
        apply PConeMorphism.ext
        rw [PConeMorphism.comp]
        dsimp
        rw [e.inv_hom_id]
        rfl

structure IsPLimit (t : PCone F a) where
  lift : ∀ s : PCone F a, s.pt ⟶ t.pt
  fac : ∀ (s : PCone F a) (j : J), prod.map (𝟙 a) (lift s) ≫ t.π.app j = s.π.app j := by aesop_cat
  uniq : ∀ (s : PCone F a) (m : s.pt ⟶ t.pt) (_ : ∀ j : J, prod.map (𝟙 a) m ≫ t.π.app j = s.π.app j), m = lift s := by
    aesop_cat

structure PLimitCone (F : J ⥤ C) (a : C) where
  cone : PCone F a
  isPLimit : IsPLimit cone

class HasPLimit (F : J ⥤ C) (a : C) : Prop where mk' ::
  exists_plimit : Nonempty (PLimitCone F a)

def HasPLimit.mk {F : J ⥤ C} {a : C} (d : PLimitCone F a) : HasPLimit F a := ⟨⟨d⟩⟩

section

variable (J C)

class HasPLimitsOfShape (a : C) : Prop where
  has_plimit : ∀ (F : J ⥤ C), HasPLimit F a := by infer_instance

end

section

variable (F a)
variable [HasPLimit F a]

def getPLimitCone :  PLimitCone F a :=
  Classical.choice <| HasPLimit.exists_plimit

def plimit.cone : PCone F a := (getPLimitCone F a).cone

def plimit : C := (plimit.cone F a).pt

def plimit.π (j : J) : a ⨯ (plimit F a) ⟶ F.obj j :=
  (plimit.cone F a).π.app j

def plimit.lift (s : PCone F a) : s.pt ⟶ plimit F a :=
  (getPLimitCone F a).isPLimit.lift s

def plimit.isPLimit : IsPLimit (plimit.cone F a) :=
  (getPLimitCone F a).isPLimit

end

def ones (b : C) : Discrete Unit ⥤ C := Functor.fromPUnit b

abbrev ExpFan (a b : C) := PCone (ones b) a

abbrev ExpFan.eval (s : ExpFan a b) : a ⨯ s.pt ⟶ b := s.π.app ⟨⟨⟩⟩

theorem ExpFan.π_app_unit (s : ExpFan a b) : s.π.app ⟨unit⟩ = s.eval := rfl

def ExpFan.ext {c c' : ExpFan a b} (e : c.pt ≅ c'.pt) (h : c.eval = prod.map (𝟙 _) e.hom ≫ c'.eval) : c ≅ c' :=
  PCone.ext e (fun j => by
    cases j
    exact h)

abbrev ExpFan.mk (g : a ⨯ c ⟶ b) : ExpFan a b where
  pt := c
  π := {
    app := fun j => g
    naturality := by aesop_cat
  }

lemma ExpFan.mk_eval (g : a ⨯ c ⟶ b) :
    (ExpFan.mk g).eval = g := by
  rfl

abbrev HasExponential (a b : C) := HasPLimit (ones b) a

noncomputable abbrev exp (a b : C) [HasExponential a b] : C := plimit (ones b) a

notation:20 a " ⇨' " b:20 => exp a b

variable (C)
abbrev HasExponentials := ∀ (a b : C), HasExponential a b
variable {C}

variable [HasExponentials C]

noncomputable abbrev exp.eval : a ⨯ a ⇨' b ⟶ b := plimit.π (ones b) a ⟨.unit⟩

variable {a b c : C}

abbrev exp.curry (g : a ⨯ c ⟶ b) : c ⟶ a ⇨' b := plimit.lift (ones b) a (ExpFan.mk g)
abbrev exp.uncurry (g : c ⟶ a ⇨' b) : a ⨯ c ⟶ b := prod.map (𝟙 _) g ≫ eval

lemma exp.fac (s : ExpFan a b) :
    prod.map (𝟙 a) (curry s.eval) ≫ eval = s.eval := plimit.isPLimit (ones b) a |>.fac s ⟨.unit⟩
lemma exp.uniq (s : ExpFan a b) (m : s.pt ⟶ exp a b)
    (h : prod.map (𝟙 a) m ≫ eval = s.eval) : m = curry s.eval := by
  apply plimit.isPLimit (ones b) a |>.uniq
  rintro ⟨PUnit.unit⟩
  apply h

theorem exp.fac' (g : a ⨯ c ⟶ b) :
    uncurry (curry g) = g := by
  rw [← ExpFan.mk_eval g]
  apply fac
theorem exp.uniq' (g : a ⨯ c ⟶ b) (m : c ⟶ a ⇨' b)
    (h : uncurry m = g) : m = curry g := by
  rw [← ExpFan.mk_eval g]
  apply uniq (ExpFan.mk g)
  apply h

def exp.prodEquiv : (a ⨯ c ⟶ b) ≃ (c ⟶ a ⇨' b) where
  toFun := curry
  invFun := uncurry
  left_inv := fac'
  right_inv := by
    rintro g
    symm
    apply uniq'
    rfl

lemma exp.uncurry_id {a b : C} :uncurry (𝟙 (a ⇨' b)) = eval := by
  rw [uncurry, prod.map_id_id, id_comp]

lemma exp.curry_eval {a b : C}: curry eval = 𝟙 (a ⇨' b) := by
  symm
  apply uniq'
  apply uncurry_id

lemma exp.uncurry_comp {a X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ a ⇨' Z}:
    uncurry (f ≫ g) = prod.map (𝟙 a) f ≫ uncurry g := by
  rw [uncurry, prod.map_id_comp, assoc, ← uncurry]

lemma exp.map_curry_uncurry_curry {X Y Z : C} {f : a ⨯ X ⟶ Y} {g : Y ⟶ Z}:
    prod.map (𝟙 a) (curry f) ≫ uncurry (curry (eval ≫ g)) = f ≫ g := by
  rw [fac' _, ← assoc, ← uncurry, fac' _]

lemma exp.uncurry_curry_comp {X Y Z : C} {f : a ⨯ X ⟶ Y} {g : Y ⟶ Z} :
    uncurry (curry f ≫ curry (eval ≫ g)) = f ≫ g := by
  rw [uncurry_comp, map_curry_uncurry_curry]

def exp.functor (a : C) : C ⥤ C where
  obj := fun b => a ⇨' b
  map := fun f => curry (eval ≫ f)
  map_id := by
    rintro a'
    rw [comp_id]
    apply curry_eval
  map_comp := by
    rintro b c d g h
    symm
    apply uniq'
    rw [uncurry_curry_comp, assoc]

lemma exp.comp_curry {a X Y Z: C} (f : X ⟶ Y) (g : a ⨯ Y ⟶ Z) :
    f ≫ curry g = curry (prod.map (𝟙 a) f ≫ g) := by
  apply uniq'
  rw [uncurry_comp, fac' _]

def exp.adjunction : prod.functor.obj a ⊣ functor a where
  unit := {
    app := fun c => curry (𝟙 _)
    naturality := by
      intro X Y f
      dsimp [functor]
      rw [exp.comp_curry, comp_id]
      symm
      apply uniq'
      rw [uncurry_curry_comp, id_comp]
  }
  counit := {
    app := fun c => uncurry (𝟙 _)
    naturality := by
      intro X Y f
      dsimp [functor]
      rw [← uncurry_comp, comp_id, fac' _, uncurry_id]
  }
  left_triangle_components X := by
    dsimp [functor]
    rw [← uncurry_comp, comp_id, fac' _]
  right_triangle_components X := by
    dsimp [functor]
    rw [uncurry_id]
    rw [← curry_eval]
    apply uniq'
    rw [uncurry_curry_comp, id_comp]

example : (a ⨯ c ⟶ b) ≃ (c ⟶ a ⇨' b) := Adjunction.homEquiv exp.adjunction c b

def ExpFan.IsPLimit.mk {t : C} {eval : a ⨯ t ⟶ b}
    (lift : (s : ExpFan a b) → s.pt ⟶ t)
    (fac : ∀ (s : ExpFan a b), prod.map (𝟙 a) (lift s) ≫ eval = s.eval)
    (uniq : ∀ (s : ExpFan a b) (m : s.pt ⟶ t), prod.map (𝟙 a) m ≫ eval = s.eval → m = lift s)
  : IsPLimit (ExpFan.mk eval) where
    lift := lift
    fac := by
      intro s ⟨.unit⟩
      apply fac
    uniq := by
      intro s m hm
      apply uniq
      apply hm ⟨.unit⟩
