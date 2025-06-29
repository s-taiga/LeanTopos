import Topoi.Chapter5

open CategoryTheory Category Limits

set_option linter.unusedSectionVars false

noncomputable section

open «CH.4».«§4.2» «CH.4».«§4.3»

variable {𝓒 : Type*} [Category 𝓒]

namespace «CH.6»

namespace «§6.1»
-- Motivating topos logic

end «§6.1»

namespace «§6.2»
-- Propositions and truth-values

-- inductive Two | Zero | One

-- instance : One Two := ⟨.One⟩
-- instance : Zero Two := ⟨.Zero⟩

abbrev Two := Fin 2

namespace Two

abbrev negation : Two → Two
  | 0 => 1
  | 1 => 0
prefix:80 "¬ₚ " => negation

abbrev conjunction : Two → Two → Two
  | 1, 1 => 1
  | _, _ => 0
infixl:60 " ∩ₚ " => conjunction

abbrev disjunction : Two → Two → Two
  | 0, 0 => 0
  | _, _ => 1
infixl:60 " ∪ₚ " => disjunction

abbrev implication : Two → Two → Two
  | 1, 0 => 0
  | _, _ => 1
infixl:60 " ⇒ₚ " => implication

def tautology {n : Nat} (predicate : Vector Two n → Two) : Prop :=
  ∀ (v : Vector Two n), predicate v = 1

def tauto₁ : Vector Two 1 → Two
  | ⟨⟨[α]⟩, _⟩ => α ∪ₚ ¬ₚ α

lemma tauto₁.tautology : tautology tauto₁ := by
  intro v
  dsimp [tauto₁]
  match v with
  | ⟨⟨[α]⟩, _⟩ =>
    match α with
    | 0 => rfl
    | 1 => rfl

def tauto₂ : Vector Two 1 → Two
  | ⟨⟨[α]⟩, _⟩ => α ⇒ₚ (α ∩ₚ α)

lemma tauto₂.tautology : tautology tauto₂ := by
  intro v
  dsimp [tauto₂]
  match v with
  | ⟨⟨[α]⟩, _⟩ =>
    match α with
    | 0 => rfl
    | 1 => rfl

def tauto₃ : Vector Two 2 → Two
  | ⟨⟨[α, β]⟩, _⟩ => β ⇒ₚ (α ⇒ₚ β)

lemma tauto₃.tautology : tautology tauto₃ := by
  intro v
  dsimp [tauto₃]
  match v with
  | ⟨⟨[α, β]⟩, _⟩ =>
    match α, β with
    | 0, 0 => rfl
    | 0, 1 => rfl
    | 1, 0 => rfl
    | 1, 1 => rfl

def tauto₄ : Vector Two 2 → Two
  | ⟨⟨[α, β]⟩, _⟩ => α ⇒ₚ (α ∪ₚ β)

lemma tauto₄.tautology : tautology tauto₄ := by
  intro v
  dsimp [tauto₄]
  match v with
  | ⟨⟨[α, β]⟩, _⟩ =>
    match α, β with
    | 0, 0 => rfl
    | 0, 1 => rfl
    | 1, 0 => rfl
    | 1, 1 => rfl

end Two

end «§6.2»

open «§6.2»

namespace «§6.3»
-- The Propositional calculus

-- Φ₀
structure «propositional variables» where
  n: Nat
notation "Φ₀" => «propositional variables»

-- Formation Rules for PL-sentences

-- Φ
inductive «PL-sentence»
  -- (1)
  | var : «propositional variables» → «PL-sentence»
  -- (2)
  | negation : «PL-sentence» → «PL-sentence»
  -- (3)
  | conjunction : «PL-sentence» → «PL-sentence» → «PL-sentence»
  | disjunction : «PL-sentence» → «PL-sentence» → «PL-sentence»
  | implication : «PL-sentence» → «PL-sentence» → «PL-sentence»
notation "Φ" => «PL-sentence»

namespace «PL-sentence»

def π' (n : Nat) : «propositional variables» := ⟨n⟩
def π (n : Nat) : «PL-sentence» := var (π' n)
prefix:80 "~ₚₗ " => negation
infixl:60 " ∧ₚₗ " => conjunction
infixl:60 " ∨ₚₗ " => disjunction
infixr:60 " ⊃ₚₗ " => implication

#check (~ₚₗ (π 2 ∧ₚₗ π 11) ∨ₚₗ (π 0 ⊃ₚₗ π 0))

abbrev V (V' : Φ₀ → Two) : Φ → Two
  | var n => V' n
  -- (a)
  | ~ₚₗ p => ¬ₚ (V V' p)
  -- (b)
  | p ∧ₚₗ q => V V' p ∩ₚ V V' q
  -- (c)
  | p ∨ₚₗ q => V V' p ∪ₚ V V' q
  -- (d)
  | p ⊃ₚₗ q => V V' p ⇒ₚ V V' q

namespace Example

def V' : Φ₀ → Two
  | ⟨0⟩ => 1
  | ⟨1⟩ => 1
  | ⟨2⟩ => 0
  -- NOTE: 使わない値なので指定したくないが、partialにすると展開されなくなるので暫定の値を入れている
  | _ => 0

example : V V' (~ₚₗ π 1) = 0 := rfl
example : V V' (~ₚₗ π 1 ∧ₚₗ π 2) = 0 := rfl
example : V V' (π 0 ⊃ₚₗ (~ₚₗ π 1 ∧ₚₗ π 2)) = 0 := rfl

end Example

def tautology (α : Φ) : Prop := ∀ (V' : Φ₀ → Two), V V' α = 1
abbrev «classical valid» := tautology

prefix:50 "⊨ₚₗ " => tautology

-- Axiomatics


namespace CL

-- NOTE: detachで使いにくいためAnd条件系をカリー化した
inductive Axiom : Φ → Prop where
  | I : ∀ α, Axiom (α ⊃ₚₗ (α ∧ₚₗ α))
  | II : ∀ α β, Axiom ((α ∧ₚₗ β) ⊃ₚₗ (β ∧ₚₗ α))
  | III : ∀ α β γ, Axiom ((α ⊃ₚₗ β) ⊃ₚₗ ((α ∧ₚₗ γ) ⊃ₚₗ (β ∧ₚₗ γ)))
  -- | IV : ∀ α β γ, Axiom (((α ⊃ₚₗ β) ∧ₚₗ (β ⊃ₚₗ γ)) ⊃ₚₗ (α ⊃ₚₗ γ))
  | IV : ∀ α β γ, Axiom ((α ⊃ₚₗ β) ⊃ₚₗ (β ⊃ₚₗ γ) ⊃ₚₗ (α ⊃ₚₗ γ))
  | V : ∀ α β, Axiom (β ⊃ₚₗ (α ⊃ₚₗ β))
  | VI : ∀ α β, Axiom ((α ∧ₚₗ (α ⊃ₚₗ β)) ⊃ₚₗ β)
  | VII : ∀ α β, Axiom (α ⊃ₚₗ (α ∨ₚₗ β))
  | VIII : ∀ α β, Axiom ((α ∨ₚₗ β) ⊃ₚₗ (β ∨ₚₗ α))
  -- | IX : ∀ α β γ, Axiom (((α ⊃ₚₗ γ) ∧ₚₗ (β ⊃ₚₗ γ)) ⊃ₚₗ ((α ∨ₚₗ β) ⊃ₚₗ γ))
  | IX : ∀ α β γ, Axiom ((α ⊃ₚₗ γ) ⊃ₚₗ (β ⊃ₚₗ γ) ⊃ₚₗ ((α ∨ₚₗ β) ⊃ₚₗ γ))
  | X : ∀ α β, Axiom (~ₚₗ α ⊃ₚₗ (α ⊃ₚₗ β))
  -- | XI : ∀ α β, Axiom (((α ⊃ₚₗ β) ∧ₚₗ (α ⊃ₚₗ ~ₚₗ β)) ⊃ₚₗ ~ₚₗ α)
  | XI : ∀ α β, Axiom ((α ⊃ₚₗ β) ⊃ₚₗ (α ⊃ₚₗ ~ₚₗ β) ⊃ₚₗ ~ₚₗ α)
  | XII : ∀ α, Axiom (α ∨ₚₗ ~ₚₗ α)
  -- NOTE: 足りないと思われる公理追加
  | A_I : ∀ α β, Axiom ((α ∧ₚₗ β) ⊃ₚₗ α)

end CL

inductive Cinf {Axiom : Φ → Prop} : Φ → Prop where
  | axiom' : ∀ {α : Φ}, Axiom α → Cinf α
  | detach : ∀ {α β : Φ}, Cinf α → Cinf (α ⊃ₚₗ β) → Cinf β
def Cinf.theorem (α : Φ) : Prop := Cinf α (Axiom := CL.Axiom)
prefix:50 "⊢ᶜˡ " => Cinf.theorem

lemma two_1_imp {α : Two} : 1 ⇒ₚ α = 1 → α = 1 := by
  intro h
  match α with
  | 0 => contradiction
  | 1 => exact h

theorem «Soundness Theorem» : ∀ α, ⊢ᶜˡ α → ⊨ₚₗ α := by
  intro α hinf V'
  induction hinf with
  | axiom' h =>
    match h with
    | .I α' =>
      dsimp [V]
      match V V' α' with
      | 0 => rfl
      | 1 => rfl
    | .II α' β' =>
      dsimp [V]
      match V V' α', V V' β' with
      | 0, 0 => rfl
      | 0, 1 => rfl
      | 1, 0 => rfl
      | 1, 1 => rfl
    | .III α' β' γ' =>
      dsimp [V]
      match V V' α', V V' β', V V' γ' with
      | 0, 0, 0 => rfl
      | 0, 0, 1 => rfl
      | 0, 1, 0 => rfl
      | 0, 1, 1 => rfl
      | 1, 0, 0 => rfl
      | 1, 0, 1 => rfl
      | 1, 1, 0 => rfl
      | 1, 1, 1 => rfl
    | .IV α' β' γ' =>
      dsimp [V]
      match V V' α', V V' β', V V' γ' with
      | 0, 0, 0 => rfl
      | 0, 0, 1 => rfl
      | 0, 1, 0 => rfl
      | 0, 1, 1 => rfl
      | 1, 0, 0 => rfl
      | 1, 0, 1 => rfl
      | 1, 1, 0 => rfl
      | 1, 1, 1 => rfl
    | .V α' β' =>
      dsimp [V]
      match V V' α', V V' β' with
      | 0, 0 => rfl
      | 0, 1 => rfl
      | 1, 0 => rfl
      | 1, 1 => rfl
    | .VI α' β' =>
      dsimp [V]
      match V V' α', V V' β' with
      | 0, 0 => rfl
      | 0, 1 => rfl
      | 1, 0 => rfl
      | 1, 1 => rfl
    | .VII α' β' =>
      dsimp [V]
      match V V' α', V V' β' with
      | 0, 0 => rfl
      | 0, 1 => rfl
      | 1, 0 => rfl
      | 1, 1 => rfl
    | .VIII α' β' =>
      dsimp [V]
      match V V' α', V V' β' with
      | 0, 0 => rfl
      | 0, 1 => rfl
      | 1, 0 => rfl
      | 1, 1 => rfl
    | .IX α' β' γ' =>
      dsimp [V]
      match V V' α', V V' β', V V' γ' with
      | 0, 0, 0 => rfl
      | 0, 0, 1 => rfl
      | 0, 1, 0 => rfl
      | 0, 1, 1 => rfl
      | 1, 0, 0 => rfl
      | 1, 0, 1 => rfl
      | 1, 1, 0 => rfl
      | 1, 1, 1 => rfl
    | .X α' β' =>
      dsimp [V]
      match V V' α', V V' β' with
      | 0, 0 => rfl
      | 0, 1 => rfl
      | 1, 0 => rfl
      | 1, 1 => rfl
    | .XI α' β' =>
      dsimp [V]
      match V V' α', V V' β' with
      | 0, 0 => rfl
      | 0, 1 => rfl
      | 1, 0 => rfl
      | 1, 1 => rfl
    | .XII α' =>
      dsimp [V]
      match V V' α' with
      | 0 => rfl
      | 1 => rfl
    | .A_I α' β' =>
      dsimp [V]
      match V V' α', V V' β' with
      | 0, 0 => rfl
      | 0, 1 => rfl
      | 1, 0 => rfl
      | 1, 1 => rfl
  | detach h₁ h₂ vα vαβ =>
    dsimp [V] at vαβ
    rw [vα] at vαβ
    apply two_1_imp vαβ

theorem «Completeness Theorem» : ∀ α, ⊨ₚₗ α → ⊢ᶜˡ α := sorry

end «PL-sentence»

end «§6.3»

namespace «§6.4»
-- Boolean algebra

variable {P : Type*} [Lattice P]

#check λ x y : P ↦ x ⊓ y
#check λ x y : P ↦ x ⊔ y

namespace «Example 1»

open Set

variable {D : Type*}

example : (⊤ : Set D) = univ := rfl
example : (⊥ : Set D) = ∅ := rfl
example (x y : Set D) : x ⊓ y = x ∩ y := rfl
example (x y : Set D) : x ⊔ y = x ∪ y := rfl

end «Example 1»

@[ext]
structure lehom (x y : P) where
  _x : P
  _y : P
  hx : x = _x
  hy : y = _y
  hom : x ≤ y

def lehom.mk' {x y : P} (f : x ≤ y) : lehom x y :=
  ⟨x, y, rfl, rfl, f⟩

def lehom.id (x : P) : lehom x x := mk' le_rfl
def lehom.comp {x y z : P} (f : lehom x y) (g : lehom y z) : lehom x z := mk' <| f.hom.trans g.hom

lemma lehom.x {x y : P} (f : lehom x y) : f._x = x := f.hx.symm
lemma lehom.y {x y : P} (f : lehom x y) : f._y = y := f.hy.symm

instance : Category P where
  Hom := lehom
  id := lehom.id
  comp := lehom.comp
  id_comp := by
    intro X Y f
    ext
    . rw [lehom.x f]
      rfl
    rw [lehom.y f]
    rfl
  comp_id := by
    intro X Y f
    ext
    . rw [lehom.x f]
      rfl
    rw [lehom.y f]
    rfl

lemma lehom.mk_eq {x y : P} (f : lehom x y) : f = mk' f.hom := by
  ext
  simp [lehom.x]
  simp [lehom.y]

lemma lehom.comp_eq {x y z : P} (f : x ≤ y) (g : y ≤ z) : (mk' f ≫ mk' g : x ⟶ z) = mk' (f.trans g) := rfl

instance lehom.prod : HasBinaryProducts P := by
  constructor
  intro F
  let X : P := F.obj ⟨.left⟩
  let Y : P := F.obj ⟨.right⟩
  let cone : Cone F := {
    pt := X ⊓ Y
    π := {
      app S := mk' <| by
        match S with
        | ⟨.left⟩ => apply inf_le_left
        | ⟨.right⟩ => apply inf_le_right
      naturality := by
        intro S₁ S₂ f
        dsimp
        match S₁, S₂ with
        | ⟨.left⟩, ⟨.left⟩ =>
          rw [id_comp, Discrete.functor_map_id, comp_id]
        | ⟨.right⟩, ⟨.right⟩ =>
          rw [id_comp, Discrete.functor_map_id, comp_id]
        | ⟨.left⟩, ⟨.right⟩ =>
          rw [id_comp]
          rfl
        | ⟨.right⟩, ⟨.left⟩ =>
          rw [id_comp]
          rfl
    }
  }
  apply HasLimit.mk
  apply show LimitCone F from {
    cone := cone
    isLimit := {
      lift s := mk' <| by
        let x' : s.pt ≤ X := s.π.app ⟨.left⟩ |>.hom
        let y' : s.pt ≤ Y := s.π.app ⟨.right⟩ |>.hom
        apply le_inf x' y'
      fac s := λ
        | ⟨.left⟩ => by
          let fst : X ⊓ Y ⟶ X := cone.π.app ⟨.left⟩
          let sfst : s.pt ⟶ X := s.π.app ⟨.left⟩
          have : cone.π.app ⟨.left⟩ = mk' fst.hom := lehom.mk_eq fst
          rw [this]
          have : s.π.app ⟨.left⟩ = mk' sfst.hom := lehom.mk_eq sfst
          rw [this]
          rw [lehom.comp_eq]
        | ⟨.right⟩ => by
          let snd : X ⊓ Y ⟶ Y := cone.π.app ⟨.right⟩
          let ssnd : s.pt ⟶ Y := s.π.app ⟨.right⟩
          have : cone.π.app ⟨.right⟩ = mk' snd.hom := lehom.mk_eq snd
          rw [this]
          have : s.π.app ⟨.right⟩ = mk' ssnd.hom := lehom.mk_eq ssnd
          rw [lehom.comp_eq]
          rw [this]
      uniq s m hm := by
        rw [lehom.mk_eq m]
    }
  }

instance lehom.coprod : HasBinaryCoproducts P := by
  constructor
  intro F
  let X : P := F.obj ⟨.left⟩
  let Y : P := F.obj ⟨.right⟩
  let cocone : Cocone F := {
    pt := X ⊔ Y
    ι := {
      app S := mk' <| by
        match S with
        | ⟨.left⟩ => apply le_sup_left
        | ⟨.right⟩ => apply le_sup_right
      naturality := by
        intro S₁ S₂ f
        dsimp
        match S₁, S₂ with
        | ⟨.left⟩, ⟨.left⟩ => rw [comp_id, Discrete.functor_map_id, id_comp]
        | ⟨.right⟩, ⟨.right⟩ => rw [comp_id, Discrete.functor_map_id, id_comp]
        | ⟨.left⟩, ⟨.right⟩ => rw [comp_id]; rfl
        | ⟨.right⟩, ⟨.left⟩ => rw [comp_id]; rfl
    }
  }
  apply HasColimit.mk
  apply show ColimitCocone F from {
    cocone := cocone
    isColimit := {
      desc s := mk' <| by
        let x' : X ≤ s.pt := s.ι.app ⟨.left⟩ |>.hom
        let y' : Y ≤ s.pt := s.ι.app ⟨.right⟩ |>.hom
        apply sup_le x' y'
      fac s := λ
        | ⟨.left⟩ => by
          have h₁ : cocone.ι.app ⟨.left⟩ = mk' (cocone.ι.app ⟨.left⟩).hom := mk_eq _
          have h₂ : s.ι.app ⟨.left⟩ = mk' (s.ι.app ⟨.left⟩).hom := mk_eq _
          rw [h₁, h₂, comp_eq]
        | ⟨.right⟩ => by
          have h₁ : cocone.ι.app ⟨.right⟩ = mk' (cocone.ι.app ⟨.right⟩).hom := mk_eq _
          have h₂ : s.ι.app ⟨.right⟩ = mk' (s.ι.app ⟨.right⟩).hom := mk_eq _
          rw [h₁, h₂, comp_eq]
      uniq s m hm := by
        rw [mk_eq m]
    }
  }

lemma lehom.hom_eq {x y : P} {f g : lehom x y} : f = g := by
  rw [lehom.mk_eq f, lehom.mk_eq g]

section

variable [BoundedOrder P]

instance lehom.initial : HasInitial P := by
  have hnonempty Y : Nonempty ((⊥ : P) ⟶ Y) := ⟨mk' bot_le⟩
  have hsingleton Y : Subsingleton ((⊥ : P) ⟶ Y) := by
    constructor
    intro f g
    apply lehom.hom_eq
  apply hasInitial_of_unique ⊥

instance lehom.terminal : HasTerminal P := by
  have hnonempty Y : Nonempty (Y ⟶ (⊤ : P)) := ⟨mk' le_top⟩
  have hsingleton Y : Subsingleton (Y ⟶ (⊤ : P)) := by
    constructor
    intro f g
    apply lehom.hom_eq
  apply hasTerminal_of_unique ⊤

end

instance lehom.pullback : HasPullbacks P := by
  have : ∀ {X Y Z : P} {f : X ⟶ Z} {g : Y ⟶ Z}, HasLimit (cospan f g) := by
    intro X Y Z f g
    let F := cospan f g
    have f' : X ≤ Z := f.hom
    apply HasLimit.mk
    let cone : Cone F := {
      pt := X ⊓ Y
      π := {
        app S := mk' <| by
          match S with
          | .left => apply inf_le_left
          | .right => apply inf_le_right
          | .one => apply inf_le_left.trans f'
        naturality := by
          intro S₁ S₂ h
          dsimp
          rw [id_comp]
          match S₁, S₂ with
          | .left, .left | .right, .right | .one, .one =>
            cases h
            simp [CategoryTheory.Functor.map_id, comp_id]
          | .left, .right | .right, .left => cases h
          | .left, .one =>
            cases h
            rw [cospan_map_inl]
            rfl
          | .right, .one =>
            cases h
            rw [cospan_map_inr]
            rfl
      }
    }
    apply show LimitCone F from {
      cone := cone
      isLimit := {
        lift s := mk' <| by
          let x' : s.pt ≤ X := s.π.app .left |>.hom
          let y' : s.pt ≤ Y := s.π.app .right |>.hom
          apply le_inf x' y'
        fac s := λ
          | .left => by
            have h₁ : cone.π.app .left = mk' (cone.π.app .left).hom := mk_eq (cone.π.app .left)
            have h₂ : s.π.app .left = mk' (s.π.app .left).hom := mk_eq (s.π.app .left)
            rw [h₁, h₂, comp_eq]
          | .right => by
            have h₁ : cone.π.app .right = mk' (cone.π.app .right).hom := mk_eq (cone.π.app .right)
            have h₂ : s.π.app .right = mk' (s.π.app .right).hom := mk_eq (s.π.app .right)
            rw [h₁, h₂, comp_eq]
          | .one => by
            have h₁ : cone.π.app .one = mk' (cone.π.app .one).hom := mk_eq (cone.π.app .one)
            have h₂ : s.π.app .one = mk' (s.π.app .one).hom := mk_eq (s.π.app .one)
            rw [h₁, h₂, comp_eq]
        uniq s m hm := by
          rw [mk_eq m]
      }
    }
  apply hasPullbacks_of_hasLimit_cospan

section

variable {P': Type*} [DistribLattice P'] {x y z : P'}
-- PをそのままDistribLatticeにするとダメだったので新しい型にする
theorem «(a)» : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := inf_sup_left x y z
theorem «(a')» : (x ⊔ y) ⊓ z = (x ⊓ z) ⊔ (y ⊓ z) := inf_sup_right x y z
theorem «(b)» : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) := sup_inf_left x y z
theorem «(b')» : (x ⊓ y) ⊔ z = (x ⊔ z) ⊓ (y ⊔ z) := sup_inf_right x y z

end

section

variable [BoundedOrder P]

theorem «complemented» {x y : P} : IsCompl x y ↔ x ⊔ y = ⊤ ∧ x ⊓ y = ⊥ :=
  isCompl_iff.trans (by
    constructor
    . intro ⟨hd, hc⟩
      constructor
      . apply le_antisymm
        . apply le_top
        apply hc le_sup_left le_sup_right
      apply le_antisymm
      . apply hd inf_le_left inf_le_right
      apply bot_le
    intro ⟨hd, hc⟩
    constructor
    . intro z hx hy
      rw [← hc]
      apply le_inf hx hy
    intro z hx hy
    rw [← hd]
    apply sup_le hx hy)

end

section

variable {P : Type*} [DistribLattice P] [BoundedOrder P]

theorem «Exercise 1» {x y z : P} : x ⊓ y = ⊥ ∧ x ⊓ z = ⊥ ∧ x ⊔ y = ⊤ ∧ x ⊔ z = ⊤ → y = z := by
  intro ⟨hyinf, hzinf, hysup, hzsup⟩
  calc
    y
    _ = y ⊓ (x ⊔ y) := by rw [sup_comm, inf_sup_self]
    _ = y ⊓ (x ⊔ z) := by rw [hysup, hzsup]
    _ = x ⊓ y ⊔ y ⊓ z := by rw [inf_comm x, «(a)»]
    _ = x ⊓ z ⊔ y ⊓ z := by rw [hyinf, hzinf]
    _ = z ⊓ x ⊔ z ⊓ y := by simp [inf_comm]
    _ = z ⊓ (x ⊔ y) := by rw [«(a)»]
    _ = z := by rw [hysup, inf_top_eq]

end

variable {P : Type*} [BooleanAlgebra P]

lemma compl_sup {x : P} : x ⊔ xᶜ = ⊤ := sup_compl_eq_top
lemma compl_inf {x : P} : x ⊓ xᶜ = ⊥ := inf_compl_eq_bot

namespace «Exercise 2»

variable {x y : P}

theorem «(1)» : (xᶜ)ᶜ = x := by
  have h₁ : xᶜ ⊓ xᶜᶜ = ⊥ := compl_inf
  have h₂ : xᶜ ⊓ x = ⊥ := inf_comm x _ ▸ compl_inf
  have h₃ : xᶜ ⊔ xᶜᶜ = ⊤ := compl_sup
  have h₄ : xᶜ ⊔ x = ⊤ := sup_comm x _ ▸ compl_sup
  apply «Exercise 1» ⟨h₁, h₂, h₃, h₄⟩

theorem «(2)» : x ⊓ y = ⊥ ↔ y ≤ xᶜ := by
  constructor
  . intro h
    have h' : xᶜ = xᶜ ⊔ y := by
      calc
        xᶜ
        _ = xᶜ ⊔ (x ⊓ y) := by rw [h, sup_comm, bot_sup_eq]
        _ = (xᶜ ⊔ x) ⊓ (xᶜ ⊔ y) := by rw [«(b)»]
        _ = ⊤ ⊓ (xᶜ ⊔ y) := by rw [sup_comm, compl_sup]
        _ = xᶜ ⊔ y := by rw [top_inf_eq]
    rw [h']
    apply le_sup_right
  intro h
  apply le_antisymm
  . rw [← compl_inf (x := x)]
    apply le_inf
    . apply inf_le_left
    apply inf_le_right.trans h
  apply bot_le

theorem «(3)» : x ≤ y ↔ yᶜ ≤ xᶜ := by
  have {x y : P} : x ≤ y → yᶜ ≤ xᶜ := by
    intro h
    apply «(2)».mp
    rw [← «(1)» (x := y)] at h
    have := «(2)».mpr h
    rw [inf_comm]
    apply this
  constructor
  apply this
  intro h
  have := this h
  simp only [«(1)»] at this
  apply this

theorem «(4)» : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ := by
  apply le_antisymm
  . apply «(3)».mpr
    rw [«(1)»]
    apply le_inf
    . apply «(3)».mpr
      rw [«(1)»]
      apply le_sup_left
    apply «(3)».mpr
    rw [«(1)»]
    apply le_sup_right
  apply sup_le
  . apply «(3)».mp
    apply inf_le_left
  apply «(3)».mp
  apply inf_le_right

theorem «(5)» : (x ⊔ y)ᶜ = xᶜ ⊓ yᶜ := by
  have := «(4)» (x := xᶜ) (y := yᶜ)
  simp only [«(1)»] at this
  rw [← this, «(1)»]

end «Exercise 2»

end «§6.4»

namespace «§6.5»
-- Algebraic semantics

variable {B : Type*} [BooleanAlgebra B]

def BAimp (x y : B) : B := xᶜ ⊔ y
infixl:60 " ⇒ᵇᵃ " => BAimp

open «CH.6».«§6.3».«PL-sentence»

theorem «Exercise 1» {V' : Φ₀ → Two} {α β : Φ} : V V' (α ⊃ₚₗ β) = V V' (~ₚₗ α ∨ₚₗ β) := by
  dsimp [V]
  match V V' α, V V' β with
  | 0, 0 => rfl
  | 0, 1 => rfl
  | 1, 0 => rfl
  | 1, 1 => rfl

def V (V' : Φ₀ → B) : Φ → B
  | var n => V' n
  -- (a)
  | ~ₚₗ p => (V V' p)ᶜ
  -- (b)
  | p ∧ₚₗ q => V V' p ⊓ V V' q
  -- (c)
  | p ∨ₚₗ q => V V' p ⊔ V V' q
  -- (d)
  | p ⊃ₚₗ q => V V' p ⇒ᵇᵃ V V' q

def tautology (B : Type*) (α : Φ) [BooleanAlgebra B] : Prop := ∀ (V' : Φ₀ → B), V V' α = ⊤
abbrev «B-valid» (B : Type*) [BooleanAlgebra B] := tautology (B := B)
infix:50 " ⊨ᵇᵃ " => tautology

lemma self_inf (a : B) : a ⊓ a = a := by
  apply le_antisymm
  . apply inf_le_left
  apply le_inf
  <;> apply le_refl

theorem «Soundness Theorem For B-Validity» : ∀ α, ⊢ᶜˡ α → B ⊨ᵇᵃ α := by
  intro α hinf V'
  induction hinf with
  | axiom' h =>
    match h with
    | .I α' =>
      dsimp [V, BAimp]
      rw [self_inf, compl_sup_eq_top]
    | .II α' β' =>
      dsimp [V, BAimp]
      rw [
        «§6.4».«Exercise 2».«(4)», «§6.4».«(b)»,
        sup_assoc, compl_sup_eq_top, sup_top_eq,
        sup_comm, ← sup_assoc, sup_compl_eq_top, top_sup_eq, self_inf]
    | .III α' β' γ' =>
      dsimp [V, BAimp]
      set a := V V' α'
      set b := V V' β'
      set c := V V' γ'
      rw [
        «§6.4».«Exercise 2».«(5)», «§6.4».«Exercise 2».«(4)», «§6.4».«Exercise 2».«(1)», «§6.4».«(b)»,
        sup_assoc _ _ c, compl_sup_eq_top, sup_top_eq, inf_top_eq,
        «§6.4».«(b')», ← sup_assoc, ← sup_assoc, sup_compl_eq_top, top_sup_eq, top_sup_eq, top_inf_eq,
        sup_comm, sup_assoc, sup_compl_eq_top, sup_assoc, sup_top_eq, sup_top_eq
      ]
    | .IV α' β' γ' =>
      dsimp [V, BAimp]
      set a := V V' α'
      set b := V V' β'
      set c := V V' γ'
      rw [
        «§6.4».«Exercise 2».«(5)», «§6.4».«Exercise 2».«(5)»,
        «§6.4».«Exercise 2».«(1)», «§6.4».«Exercise 2».«(1)»,
        sup_comm _ c, ← sup_assoc _ c, «§6.4».«(b')» (x := b), compl_sup_eq_top, inf_top_eq,
        «§6.4».«(b')», sup_comm _ aᶜ, ← sup_assoc, sup_compl_eq_top, top_sup_eq, top_inf_eq,
        ← sup_assoc aᶜ, sup_comm aᶜ, sup_assoc, ← sup_assoc, compl_sup_eq_top, top_sup_eq
      ]
    | .V α' β' =>
      dsimp [V, BAimp]
      rw [sup_comm, sup_assoc, sup_compl_eq_top, sup_top_eq]
    | .VI α' β' =>
      dsimp [V, BAimp]
      set a := V V' α'
      set b := V V' β'
      rw [
        «§6.4».«Exercise 2».«(4)», «§6.4».«Exercise 2».«(5)», «§6.4».«Exercise 2».«(1)»,
        «§6.4».«(b)», compl_sup_eq_top, top_inf_eq, sup_assoc, compl_sup_eq_top, sup_top_eq
      ]
    | .VII α' β' =>
      dsimp [V, BAimp]
      rw [← sup_assoc, compl_sup_eq_top, top_sup_eq]
    | .VIII α' β' =>
      dsimp [V, BAimp]
      set a := V V' α'
      set b := V V' β'
      rw [
        «§6.4».«Exercise 2».«(5)», «§6.4».«(b')»,
        sup_comm, sup_assoc, sup_compl_eq_top, sup_top_eq, top_inf_eq,
        ← sup_assoc, compl_sup_eq_top, top_sup_eq
      ]
    | .IX α' β' γ' =>
      dsimp [V, BAimp]
      set a := V V' α'
      set b := V V' β'
      set c := V V' γ'
      rw [
        «§6.4».«Exercise 2».«(5)», «§6.4».«Exercise 2».«(5)»,
        «§6.4».«Exercise 2».«(1)», «§6.4».«Exercise 2».«(1)», ← sup_assoc, ← «§6.4».«(a')»,
      ]
      set d := a ⊔ b
      rw [
        «§6.4».«(b')», ← sup_assoc, sup_compl_eq_top, top_sup_eq, top_inf_eq,
        sup_comm dᶜ, ← sup_assoc, compl_sup_eq_top, top_sup_eq
      ]
    | .X α' β' =>
      dsimp [V, BAimp]
      set a := V V' α'
      set b := V V' β'
      rw [
        «§6.4».«Exercise 2».«(1)», ← sup_assoc, sup_compl_eq_top, top_sup_eq,
      ]
    | .XI α' β' =>
      dsimp [V, BAimp]
      set a := V V' α'
      set b := V V' β'
      rw [
        ← «§6.4».«Exercise 2».«(4)», ← «§6.4».«Exercise 2».«(4)»,
        «§6.4».«(a')» (y := bᶜ), compl_inf_eq_bot, bot_sup_eq,
        «§6.4».«(a')», inf_comm bᶜ, ← inf_assoc, compl_inf_eq_bot, bot_inf_eq, bot_sup_eq,
        inf_comm a, ← inf_assoc, inf_compl_eq_bot, bot_inf_eq, compl_eq_top
      ]
    | .XII α' =>
      dsimp [V, BAimp]
      apply sup_compl_eq_top
    | .A_I α' β' =>
      dsimp [V, BAimp]
      set a := V V' α'
      set b := V V' β'
      rw [«§6.4».«Exercise 2».«(4)», sup_comm, ← sup_assoc, sup_compl_eq_top, top_sup_eq]
  | detach h₁ h₂ vα vαβ =>
    dsimp [V, BAimp] at vαβ
    rw [vα, compl_top, bot_sup_eq] at vαβ
    apply vαβ

theorem «Completeness Theorem For B-Validity» : ∀ α, B ⊨ᵇᵃ α → ⊢ᶜˡ α := sorry

namespace «Exercise 2»

abbrev Vtwo := «§6.3».«PL-sentence».V

def c_equivalence (α β : Φ) : Prop := ⊢ᶜˡ α ⊃ₚₗ β ∧ ⊢ᶜˡ β ⊃ₚₗ α
infix:50 " ~ᶜ " => c_equivalence

lemma cl.comp {α β γ : Φ} (hab : ⊢ᶜˡ α ⊃ₚₗ β) (hbc : ⊢ᶜˡ β ⊃ₚₗ γ) : ⊢ᶜˡ α ⊃ₚₗ γ := by
  apply Cinf.detach hbc
  apply Cinf.detach hab
  apply Cinf.axiom' (CL.Axiom.IV α β γ)

instance PL_equiv : Equivalence (· ~ᶜ ·) where
  refl α := by
    constructor
    . sorry
    sorry
  symm := by
    intro α β ⟨h₁, h₂⟩
    apply And.intro h₂ h₁
  trans := by
    intro α β γ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    constructor
    . apply cl.comp h₁ h₃
    apply cl.comp h₄ h₂

instance PL_setoid : Setoid Φ where
  r := (· ~ᶜ ·)
  iseqv := PL_equiv

abbrev la_le (α β : Quotient PL_setoid) : Prop := ⊢ᶜˡ (α.out ⊃ₚₗ β.out)

lemma Quotient.out_eq'' {A : Type*} {s : Setoid A} {a : A} : ⟦a⟧.out (s := s) = a := by
  sorry

instance «Lindenbaum Algebra» : BooleanAlgebra (Quotient PL_setoid) where
  le := la_le
  le_refl := by
    intro a
    dsimp [la_le]
    apply PL_equiv.refl a.out |>.1
  le_trans := by
    intro a b c hab hbc
    dsimp [la_le] at *
    apply cl.comp hab hbc
  le_antisymm a b := by
    intro hab hba
    dsimp [la_le] at *
    have : a.out ~ᶜ b.out := ⟨hab, hba⟩
    rw [← a.out_eq, ← b.out_eq]
    apply Quotient.eq.mpr this
  sup a b := ⟦a.out ∨ₚₗ b.out⟧
  le_sup_left a b := by
    dsimp [la_le]
    rw [Quotient.out_eq'']
    apply Cinf.axiom'
    apply CL.Axiom.VII
  le_sup_right a b := by
    dsimp [la_le]
    rw [Quotient.out_eq'']
    apply Cinf.detach <| Cinf.axiom' <| CL.Axiom.VIII b.out a.out
    apply Cinf.detach <| Cinf.axiom' <| CL.Axiom.VII b.out a.out
    apply Cinf.axiom' <| CL.Axiom.IV _ _ _
  sup_le a b c hac hbc := by
    dsimp [la_le]
    rw [Quotient.out_eq'']
    apply Cinf.detach hbc
    apply Cinf.detach hac
    apply Cinf.axiom' <| CL.Axiom.IX a.out b.out c.out
  inf a b := ⟦a.out ∧ₚₗ b.out⟧
  inf_le_left a b := by
    dsimp [la_le]
    rw [Quotient.out_eq'']
    apply Cinf.axiom' <| CL.Axiom.A_I a.out b.out
  inf_le_right a b := by
    dsimp [la_le]
    rw [Quotient.out_eq'']
    apply Cinf.detach <| Cinf.axiom' <| CL.Axiom.A_I b.out a.out
    apply Cinf.detach <| Cinf.axiom' <| CL.Axiom.II a.out b.out
    apply Cinf.axiom' <| CL.Axiom.IV _ _ _
  le_inf a b c hab hac := by
    dsimp [la_le]
    rw [Quotient.out_eq'']
    apply cl.comp
    apply Cinf.axiom' <| CL.Axiom.I a.out
    apply cl.comp
    apply Cinf.detach hac <| Cinf.axiom' <| CL.Axiom.III a.out c.out a.out
    apply cl.comp
    apply Cinf.axiom' <| CL.Axiom.II c.out a.out
    apply Cinf.detach hab
    apply Cinf.axiom' <| CL.Axiom.III a.out b.out c.out
  le_sup_inf a b c := by
    dsimp [la_le]
    sorry
  compl a := ⟦~ₚₗ a.out⟧
  sdiff a b := sorry
  himp := sorry
  top := sorry
  bot := sorry
  inf_compl_le_bot := sorry
  top_le_sup_compl := sorry
  le_top := sorry
  bot_le := sorry
  sdiff_eq := sorry
  himp_eq := sorry

end «Exercise 2»

end «§6.5»

namespace «§6.6»
-- Truth-functions as arrows

def truep : types.Hom Unit Two := λ ⟨⟩ => 1
def falsep : Unit → Two := λ ⟨⟩ => 0

lemma neg1 {x : Two} : ¬ₚ x = 1 → x = 0 := by
  match x with
  | 0 => intro h; rfl
  | 1 => intro h; contradiction

lemma Negation : IsPullback falsep id (¬ₚ ·) truep := by
  have : (falsep ≫ fun x ↦ ¬ₚ x) = id ≫ truep := by
    ext ⟨⟩
    dsimp [truep, falsep, «§6.2».Two.negation]

  let cone : PullbackCone (¬ₚ ·) truep := .mk falsep id this
  apply IsPullback.of_isLimit (c := cone)
  apply PullbackCone.IsLimit.mk this (λ s _ ↦ ⟨⟩)
  . intro s
    ext x
    dsimp [falsep]
    have := congrFun s.condition x
    dsimp [truep] at this
    rw [neg1 this]
    rfl
  . intro s
    ext x
  intro s m hmfst hmsnd
  ext x

def true2 : Unit → Two × Two := λ ⟨⟩ => (1, 1)

lemma conj1 {x : Two × Two} : x.1 ∩ₚ x.2 = 1 → x = (1, 1) := by
  match x with
  | (0, 0) => intro h; contradiction
  | (0, 1) => intro h; contradiction
  | (1, 0) => intro h; contradiction
  | (1, 1) => intro h; rfl

lemma Conjunction : IsPullback true2 id (λ x ↦ x.1 ∩ₚ x.2) truep := by
  have : (true2 ≫ λ x ↦ x.1 ∩ₚ x.2) = id ≫ truep := by
    ext ⟨⟩
    dsimp [truep, true2, «§6.2».Two.conjunction]

  let cone : PullbackCone (λ x : Two × Two ↦ x.1 ∩ₚ x.2) truep := .mk true2 id this
  apply IsPullback.of_isLimit (c := cone)
  apply PullbackCone.IsLimit.mk this (λ s _ ↦ ⟨⟩)
  . intro s
    ext x
    have h := congrFun s.condition x
    dsimp [truep] at h
    . dsimp [true2]
      rw [conj1 h]
      rfl
    have h := congrFun s.condition x
    dsimp [truep] at h
    dsimp [true2]
    rw [conj1 h]
    rfl
  . intro s
    ext x
  intro s m hmfst hmsnd
  ext x

abbrev IMP := {x : Two × Two // x.1 ≤ x.2}
abbrev imp_inj : IMP ⟶ Two × Two := Subtype.val

lemma Implication : IsPullback imp_inj (λ _ ↦ .unit) (λ x ↦ x.1 ⇒ₚ x.2) truep := by
  have : (imp_inj ≫ λ x ↦ x.1 ⇒ₚ x.2) = (λ _ ↦ .unit) ≫ truep := by
    ext x
    match x with
    | ⟨⟨0, 0⟩, _⟩ => dsimp [truep, imp_inj, «§6.2».Two.implication]
    | ⟨⟨0, 1⟩, _⟩ => dsimp [truep, «§6.2».Two.implication]
    | ⟨⟨1, 1⟩, _⟩ => dsimp [truep, imp_inj, «§6.2».Two.implication]

  let cone : PullbackCone (λ x : Two × Two ↦ x.1 ⇒ₚ x.2) truep := .mk Subtype.val (λ _ ↦ .unit) this
  apply IsPullback.of_isLimit (c := cone)
  apply PullbackCone.IsLimit.mk this (λ s x ↦ ⟨s.fst x, by
    have := congrFun s.condition x
    dsimp [truep] at this
    revert this
    match s.fst x with
    | (0, 0) => intro h; rfl
    | (0, 1) => simp
    | (1, 0) =>
      intro h
      dsimp [«§6.2».Two.implication] at h
      contradiction
    | (1, 1) => intro h; rfl
  ⟩)
  . intro s
    ext x
    . dsimp [imp_inj]
    dsimp [imp_inj]
  . intro s
    ext x
  intro s m hmfst hmsnd
  ext x
  <;> dsimp
  <;> rw [← hmfst]
  <;> dsimp [imp_inj]

lemma «why?» {P : Type*} [Lattice P] {x y : P} : x ≤ y ↔ x ⊓ y = x := by
  constructor
  . intro h
    apply le_antisymm
    . apply inf_le_left
    apply le_inf (le_refl _) h
  intro h
  rw [← h]
  apply inf_le_right

def pr1 : Two × Two ⟶ Two := Prod.fst

lemma w : imp_inj ≫ (λ x : Two × Two ↦ x.1 ∩ₚ x.2) = imp_inj ≫ pr1 := by
  ext x
  match x with
  | ⟨(0, 0), _⟩ => dsimp [imp_inj, «§6.2».Two.conjunction, pr1]
  | ⟨(0, 1), _⟩ => dsimp [imp_inj, «§6.2».Two.conjunction, pr1]
  | ⟨(1, 1), _⟩ => dsimp [imp_inj, «§6.2».Two.conjunction, pr1]

def «Implication Equalizer» : IsLimit (Fork.ofι imp_inj w) := by
  apply Fork.IsLimit.mk _ (λ s x ↦ ⟨s.ι x, by
    have := congrFun s.condition x
    dsimp [pr1] at this
    rw [← this]
    match s.ι x with
    | (0, 0) => rfl
    | (0, 1) => simp [«§6.2».Two.conjunction]
    | (1, 0) => rfl
    | (1, 1) => rfl⟩)
  . intro s
    ext x
    dsimp [imp_inj]
  intro s m hm
  ext x
  have := congrFun hm x
  dsimp [imp_inj] at this
  apply Subtype.ext_val
  rw [this]

def Amor : Two ⟶ Two × Two := λ x ↦ (1, x)
def Bmor : Two ⟶ Two × Two := λ x ↦ (x, 1)

abbrev f : Two ⨿ Two ⟶ Two × Two := coprod.desc Amor Bmor

-- abbrev D := «CH.5».«§5.2».fFactor f |>.choose
-- def imf : Two ⨿ Two ⟶ D := «CH.5».«§5.2».fFactor f |>.choose_spec |>.choose

-- Truth-arrows in a topos
open «CH.4».«§4.1»
variable {Ω : 𝓒} [ElementaryTopos Ω]

lemma element.mono {a : 𝓒} (x : element a) : Mono x := by
  apply «CH.3».«§3.6».Excercises.«3»

def negT : Ω ⟶ Ω := χ «CH.5».«§5.4».false' (element.mono _)

def conT : Ω ⨯ Ω ⟶ Ω := χ (prod.lift true true) (element.mono _)

abbrev disMor := coprod.desc ((prod.leftUnitor Ω).inv ≫ prod.map true (𝟙 Ω)) ((prod.rightUnitor Ω).inv ≫ prod.map (𝟙 Ω) true)
abbrev Dis := «CH.5».«§5.2».fa' Ω <| disMor (Ω := Ω)
def imDisT : (Dis (Ω := Ω)) ⟶ Ω ⨯ Ω := «CH.5».«§5.2».im Ω _
def disT : Ω ⨯ Ω ⟶ Ω := χ imDisT <| «CH.5».«§5.2».monoImage Ω _

abbrev ImpT : 𝓒 := equalizer (conT (Ω := Ω)) prod.fst
abbrev e : (ImpT (Ω := Ω)) ⟶ Ω ⨯ Ω := equalizer.ι conT prod.fst
def impT : Ω ⨯ Ω ⟶ Ω := χ e <| «CH.3».«§3.10».«theorem 1» _ _ _

end «§6.6»

namespace «§6.7»
-- 𝓒-semantics

open «§6.6» «CH.4».«§4.1» «CH.6».«§6.3».«PL-sentence»
variable {Ω : 𝓒} [ElementaryTopos Ω]

abbrev V (V' : Φ₀ → element Ω) : Φ → element Ω
  | var n => V' n
  | ~ₚₗ p => V V' p ≫ negT
  | p ∧ₚₗ q => prod.lift (V V' p) (V V' q) ≫ conT
  | p ∨ₚₗ q => prod.lift (V V' p) (V V' q) ≫ disT
  | p ⊃ₚₗ q => prod.lift (V V' p) (V V' q) ≫ impT

def tautology (α : Φ) : Prop := ∀ (V' : Φ₀ → element Ω), V V' α = (true (Ω := Ω))
abbrev «𝓒-valid» := tautology (Ω := Ω)
notation:80 𝓒 " (" Ω ")⊨ " α => tautology α (𝓒 := 𝓒) (Ω := Ω)

example {α : Φ} : 𝓒(Ω)⊨ α ⊃ₚₗ (α ∧ₚₗ α) := by
  intro V'
  dsimp [V]
  set a := V V' α
  set trtr := prod.lift (true (Ω := Ω)) (true (Ω := Ω))
  nth_rewrite 1 [← comp_id a]
  rw [← prod.comp_diag, assoc, ← prod.comp_lift]
  let s := χ a («§6.6».element.mono a) (Ω := Ω)
  -- have : a = prod.lift a a ≫ prod.fst := by
  --   rw [prod.lift_fst]
  -- nth_rewrite 1 [this]
  -- rw [← prod.comp_lift, ← prod.comp_diag, assoc a, prod.comp_lift, prod.lift_fst]
  -- have ⟨himpTpb, _⟩ := χ.spec «§6.6».e («CH.3».«§3.10».«theorem 1» _ (conT (Ω := Ω)) prod.fst) (Ω := Ω)
  -- have := himpTpb.w
  -- rw [← prod.comp_diag, assoc β]
  -- nth_rewrite 1 [← comp_id β]
  -- rw [← prod.comp_lift]
  sorry

namespace «𝓒-semantics»

variable (Ω)
abbrev trtr : ⊤_ 𝓒 ⟶ Ω ⨯ Ω := prod.lift true true

lemma l1 : trtr Ω ≫ conT = trtr Ω ≫ prod.fst := by
  have ⟨hconTpb, _⟩ := χ.spec (trtr Ω) («§6.6».element.mono _) (Ω := Ω)
  rw [conT, hconTpb.w, «CH.4».«§4.2».terminal.fromTiso1, id_comp, prod.lift_fst]

abbrev trtrImpT : ⊤_ 𝓒 ⟶ ImpT (Ω := Ω) := equalizer.lift (trtr _) (l1 _)

lemma l2 : trtrImpT Ω ≫ e = trtr Ω := equalizer.lift_ι _ _

lemma l3 : trtr Ω ≫ impT = true (Ω := Ω) := by
  have ⟨hePb, _⟩ := χ.spec (e (Ω := Ω)) («CH.3».«§3.10».«theorem 1» _ _ _) (Ω := Ω)
  rw [← l2, assoc, impT, hePb.w, ← assoc, terminal.comp_from, «CH.3».«§3.6».terminal_id, id_comp]

lemma l4 : trtr Ω ≫ conT = true (Ω := Ω) := by
  have ⟨hconTpb, _⟩ := χ.spec (trtr Ω) («§6.6».element.mono _) (Ω := Ω)
  rw [conT, hconTpb.w, «CH.3».«§3.6».terminal_id, id_comp]

end «𝓒-semantics»

variable (Ω)

abbrev TRUE := true (Ω := Ω)
abbrev FALSE := «CH.5».«§5.4».false' (Ω := Ω)

namespace «Theorem 1»

lemma neg_1 : TRUE Ω ≫ negT = FALSE Ω := by
  have ⟨hnegPb, _⟩ := χ.spec (FALSE Ω) («§6.6».element.mono _) (Ω := Ω)
  have : «CH.5».«§5.4».false (⊤_ 𝓒) = FALSE Ω := by
    dsimp [«CH.5».«§5.4».false, FALSE]
    rw [«CH.3».«§3.6».terminal_id, id_comp]
  -- TODO: 結構しょっちゅう使うので補題にする
  have hti : terminal.from (⊥_ 𝓒) = initial.to (⊤_ 𝓒) := by ext
  have ⟨hfalsePb', huniq⟩ := hti ▸ this ▸ «CH.5».«§5.4».«Exercise 3» (⊤_ 𝓒) ▸ χ.spec (initial.to (⊤_ 𝓒)) («CH.3».«§3.16».«Theorem 1».«(4)» _) (Ω := Ω)
  have := hfalsePb'.flip.paste_vert hnegPb
  rw [«CH.3».«§3.6».terminal_id, comp_id] at this
  apply huniq (TRUE Ω ≫ negT) this

lemma neg_2 : FALSE Ω ≫ negT = TRUE Ω := by
  have ⟨hnegPb, _⟩ := χ.spec (FALSE Ω) («§6.6».element.mono _) (Ω := Ω)
  rw [negT, hnegPb.w, «CH.3».«§3.6».terminal_id, id_comp]

notation:80 f " ∩(" Ω ") " g => prod.lift f g ≫ «§6.6».conT (Ω := Ω)
notation:80 f " ∪(" Ω ") " g => prod.lift f g ≫ «§6.6».disT (Ω := Ω)
notation:80 f " ⇒(" Ω ") " g => prod.lift f g ≫ «§6.6».impT (Ω := Ω)

-- NOTE: この内容は次章で証明されるため省略
lemma con_1 : (TRUE Ω ∩(Ω) TRUE Ω) = TRUE Ω := by sorry
lemma con_2 : (TRUE Ω ∩(Ω) FALSE Ω) = FALSE Ω := by sorry
lemma con_3 : (FALSE Ω ∩(Ω) TRUE Ω) = FALSE Ω := by sorry
lemma con_4 : (FALSE Ω ∩(Ω) FALSE Ω) = FALSE Ω := by sorry
lemma dis_1 : (TRUE Ω ∪(Ω) TRUE Ω) = TRUE Ω := by sorry
lemma dis_2 : (TRUE Ω ∪(Ω) FALSE Ω) = TRUE Ω := by sorry
lemma dis_3 : (FALSE Ω ∪(Ω) TRUE Ω) = TRUE Ω := by sorry
lemma dis_4 : (FALSE Ω ∪(Ω) FALSE Ω) = FALSE Ω := by sorry
lemma imp_1 : (TRUE Ω ⇒(Ω) TRUE Ω) = TRUE Ω := by sorry
lemma imp_2 : (TRUE Ω ⇒(Ω) FALSE Ω) = FALSE Ω := by sorry
lemma imp_3 : (FALSE Ω ⇒(Ω) TRUE Ω) = TRUE Ω := by sorry
lemma imp_4 : (FALSE Ω ⇒(Ω) FALSE Ω) = TRUE Ω := by sorry

end «Theorem 1»

variable (V : Φ₀ → Two)
abbrev V' (v : Φ₀) : element Ω :=
  match V v with
  | 1 => TRUE Ω
  | 0 => FALSE Ω

namespace «Lemma»

variable (α : Φ)
abbrev V'' := «§6.7».V (V' Ω V)

lemma «(a)» : V'' Ω V α = TRUE Ω ∨ V'' Ω V α = FALSE Ω := by
  dsimp [V'']
  induction α with
  | var n =>
    dsimp [«§6.7».V, V']
    match V n with
    | 1 =>
      dsimp
      left
      rfl
    | 0 =>
      dsimp
      right
      rfl
  | negation p h =>
    dsimp [«§6.7».V, V']
    match h with
    | .inl h =>
      rw [h]
      right
      rw [«Theorem 1».neg_1]
    | .inr h =>
      rw [h]
      left
      rw [«Theorem 1».neg_2]
  | conjunction p q hp hq =>
    dsimp [«§6.7».V, V']
    match hp, hq with
    | .inl hp, .inl hq =>
      left
      rw [hp, hq, «Theorem 1».con_1]
    | .inl hp, .inr hq | .inr hp, .inl hq | .inr hp, .inr hq =>
      right
      rw [hp, hq]
      first | rw [«Theorem 1».con_2] | rw [«Theorem 1».con_3] | rw [«Theorem 1».con_4]
  | disjunction p q hp hq =>
    dsimp [«§6.7».V, V']
    match hp, hq with
    | .inr hp, .inr hq =>
      right
      rw [hp, hq, «Theorem 1».dis_4]
    | .inl hp, .inr hq | .inr hp, .inl hq | .inl hp, .inl hq =>
      left
      rw [hp, hq]
      first | rw [«Theorem 1».dis_2] | rw [«Theorem 1».dis_3] | rw [«Theorem 1».dis_1]
  | implication p q hp hq =>
    dsimp [«§6.7».V, V']
    match hp, hq with
    | .inl hp, .inr hq =>
      right
      rw [hp, hq, «Theorem 1».imp_2]
    | .inr hp, .inr hq | .inr hp, .inl hq | .inl hp, .inl hq =>
      left
      rw [hp, hq]
      first | rw [«Theorem 1».imp_1] | rw [«Theorem 1».imp_3] | rw [«Theorem 1».imp_4]

lemma «(b)» : V'' Ω V α = TRUE Ω ↔ «§6.3».«PL-sentence».V V α = 1 := by
  induction α with
  | var n =>
    dsimp [V'', «§6.3».«PL-sentence».V, «§6.7».V, V']
    match V n with
    | 1 => dsimp; exact ⟨λ _ ↦ rfl, λ _ ↦ rfl⟩
    | 0 =>
      dsimp
      constructor
      . intro h
        -- «CH.5».«§5.4».«Exercise 4»が必要なので𝓒はWellpointedじゃないといけないのでは？
        sorry
      intro h
      contradiction
  | negation p h =>
    dsimp [V'', «§6.3».«PL-sentence».V, «§6.7».V, V']
    sorry
  | conjunction p q hp hq =>
    sorry
  | disjunction p q hp hq =>
    sorry
  | implication p q hp hq =>
    sorry

theorem «Theorem 2» : (𝓒 (Ω)⊨ α) → ⊢ᶜˡ α := by
  intro h
  have : ⊨ₚₗ α := λ V ↦ Lemma.«(b)» Ω V α |>.mp <| h (V' Ω V)
  apply «§6.3».«PL-sentence».«Completeness Theorem» _ this

theorem «Theorem 3» [«CH.5».«§5.4».WellPointed 𝓒] : (𝓒 (Ω)⊨ α) ↔ ⊢ᶜˡ α := by
  constructor
  . apply «Theorem 2»
  intro h V'
  have bv := «CH.5».«§5.4».«Theorem 2» (𝓒 := 𝓒) (Ω := Ω)
  have := bv <| «§6.7».V V' α
  -- have ht := λ V ↦ Lemma.«(b)» Ω V α |>.mpr
  -- dsimp [V''] at ht
  sorry
