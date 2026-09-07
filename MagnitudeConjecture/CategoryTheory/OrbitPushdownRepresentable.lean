import MagnitudeConjecture.CategoryTheory.DeckOrbitSkeleton
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdown
import MagnitudeConjecture.CategoryTheory.ShiftOrbitFactorization
import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# Orbit push-down of representable modules

Gabriel push-down sends the covariant linear representable at an upstairs
object to the covariant linear representable at the same object in the
shift-orbit category.  This is the projective half of the Nakayama comparison
used in preservation of Auslander--Reiten sequences.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]

instance linearCoyoneda_obj_linear (X : C) :
    ((linearCoyoneda k C).obj (Opposite.op X)).Linear k where
  map_smul f r := by
    apply ModuleCat.hom_ext
    ext g
    change g ≫ (r • f) = r • (g ≫ f)
    rw [CategoryTheory.Linear.comp_smul]

/-- The covariant linear representable as an object of the full category of
additive linear modules. -/
noncomputable def linearCoyonedaLinearModule (X : C) :
    LinearModuleCategory.{u, v, uK, v} (C := C) k :=
  ⟨(linearCoyoneda k C).obj (Opposite.op X), inferInstance, inferInstance⟩

/-- A morphism of representing objects induces the contravariant map between
the corresponding projective representables. -/
noncomputable def linearCoyonedaLinearModuleMap
    {X Z : C} (f : X ⟶ Z) :
    linearCoyonedaLinearModule (k := k) Z ⟶
      linearCoyonedaLinearModule (k := k) X :=
  ObjectProperty.homMk ((linearCoyoneda k C).map f.op)

/-- A representable known to have finite support and finite-dimensional values,
bundled in the finite-dimensional module category. -/
noncomputable def finiteDimensionalLinearCoyoneda (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k :=
  ⟨linearCoyonedaLinearModule (k := k) X, hX⟩

/-- Finite-dimensional bundled form of the map between projective
representables induced by a representing morphism. -/
noncomputable def finiteDimensionalLinearCoyonedaMap
    {X Z : C} (f : X ⟶ Z)
    (hX : IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hZ : IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) Z)) :
    finiteDimensionalLinearCoyoneda (k := k) Z hZ ⟶
      finiteDimensionalLinearCoyoneda (k := k) X hX :=
  ObjectProperty.homMk (linearCoyonedaLinearModuleMap (k := k) f)

set_option backward.isDefEq.respectTransparency false in
/-- On a representable module, the push-down action is right composition in
the shift-orbit category. -/
theorem orbitPushdownLinearCoyoneda_map
    (X Y Z : C) (f : ShiftOrbitHom A Y Z) :
    orbitPushdownMapLinear
        ((linearCoyoneda k C).obj (Opposite.op X)) f =
      (shiftOrbitCompLinearMap (k := k) (X := X) (Y := Y) (Z := Z)).flip f := by
  classical
  induction f using DirectSum.induction_on with
  | zero =>
      simp
  | of a h =>
      change orbitPushdownMapLinear
          ((linearCoyoneda k C).obj (Opposite.op X))
            (shiftOrbitOf Y Z a h) =
        (shiftOrbitCompLinearMap (k := k)
          (X := X) (Y := Y) (Z := Z)).flip (shiftOrbitOf Y Z a h)
      rw [orbitPushdownMapLinear_of]
      apply DirectSum.linearMap_ext
      intro b
      apply LinearMap.ext
      intro q
      change orbitPushdownHomogeneousMap
          ((linearCoyoneda k C).obj (Opposite.op X)) a h
            (orbitPushdownLof
              ((linearCoyoneda k C).obj (Opposite.op X)) Y b q) =
        (shiftOrbitCompLinearMap (k := k)
          (shiftOrbitOf X Y b q)) (shiftOrbitOf Y Z a h)
      rw [orbitPushdownHomogeneousMap_lof,
        shiftOrbitCompLinearMap_apply, shiftOrbitCompHom_of_of]
      rfl
  | add f₁ f₂ hf₁ hf₂ =>
      rw [map_add, map_add, hf₁, hf₂]

/-- Orbit push-down of `Hom(X,-)` is the representable module
`Hom_orbit(X,-)`. -/
noncomputable def orbitPushdownLinearCoyonedaIso (X : C) :
    orbitPushdown (A := A) ((linearCoyoneda k C).obj (Opposite.op X)) ≅
      (linearCoyoneda k (ShiftOrbitCategory C A)).obj
        (Opposite.op (show ShiftOrbitCategory C A from X)) := by
  refine NatIso.ofComponents (fun _ ↦ Iso.refl _) ?_
  intro Y Z f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  change orbitPushdownMapLinear
      ((linearCoyoneda k C).obj (Opposite.op X)) f g =
    shiftOrbitCompHom g f
  rw [orbitPushdownLinearCoyoneda_map X (show C from Y)
    (show C from Z) f]
  exact shiftOrbitCompLinearMap_apply g f

set_option backward.isDefEq.respectTransparency false in
/-- The representable push-down isomorphisms commute with morphisms of
representing objects. -/
theorem orbitPushdownLinearCoyonedaIso_representing_naturality
    {X Z : C} (f : X ⟶ Z) :
    orbitPushdownNatTrans (A := A)
        ((linearCoyoneda k C).map f.op) ≫
      (orbitPushdownLinearCoyonedaIso (k := k) (A := A) X).hom =
    (orbitPushdownLinearCoyonedaIso (k := k) (A := A) Z).hom ≫
      (linearCoyoneda k (ShiftOrbitCategory C A)).map
        ((ShiftOrbitCategory.identityComponentFunctor
          (C := C) (A := A)).map f).op := by
  classical
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro q
  change (Z ⟶ (shiftFunctor C b).obj (show C from Y)) at q
  change orbitPushdownNatTransAppLinear (A := A)
      ((linearCoyoneda k C).map f.op) (show C from Y)
        (orbitPushdownLof
          ((linearCoyoneda k C).obj (Opposite.op Z))
          (show C from Y) b q) =
    shiftOrbitCompHom
      (shiftOrbitOf X Z 0 (shiftHomZero (A := A) f))
      (shiftOrbitOf Z (show C from Y) b q)
  rw [orbitPushdownNatTransAppLinear_lof]
  change shiftOrbitOf X (show C from Y) b (f ≫ q) = _
  exact (shiftOrbitComp_zero_left_of (A := A) f q).symm

section OrbitSkeleton

variable {G : Type w} [Group G] [MulAction G C]
variable [HasShift C (Additive G)]
variable [∀ a : Additive G, (shiftFunctor C a).Additive]
variable [∀ a : Additive G, (shiftFunctor C a).Linear k]

set_option backward.isDefEq.respectTransparency false in
/-- Restricting the orbit representable at a chosen representative gives the
literal representable on the induced orbit skeleton. -/
noncomputable def deckOrbitRepresentativeLinearCoyonedaIso
    (q : MulAction.orbitRel.Quotient G C) :
    deckOrbitRepresentativeFunctor (C := C) (G := G) ⋙
        (linearCoyoneda k (ShiftOrbitCategory C (Additive G))).obj
          (Opposite.op
            (show ShiftOrbitCategory C (Additive G) from
              deckOrbitRepresentative (C := C) (G := G) q)) ≅
      (linearCoyoneda k (DeckOrbitSkeleton C G)).obj (Opposite.op q) := by
  refine NatIso.ofComponents (fun X ↦
    (InducedCategory.homLinearEquiv (R := k)
      (X := q) (Y := X)).symm.toModuleIso) ?_
  intro Y Z f
  apply ModuleCat.hom_ext
  rfl

/-- Restriction to the chosen orbit skeleton commutes with morphisms of
representing objects for projective representables. -/
theorem deckOrbitRepresentativeLinearCoyonedaIso_representing_naturality
    {q r : MulAction.orbitRel.Quotient G C}
    (f : (show DeckOrbitSkeleton C G from q) ⟶
      (show DeckOrbitSkeleton C G from r)) :
    Functor.whiskerLeft
        (deckOrbitRepresentativeFunctor (C := C) (G := G))
        ((linearCoyoneda k
          (ShiftOrbitCategory C (Additive G))).map
            ((deckOrbitRepresentativeFunctor
              (C := C) (G := G)).map f).op) ≫
      (deckOrbitRepresentativeLinearCoyonedaIso (k := k) q).hom =
    (deckOrbitRepresentativeLinearCoyonedaIso (k := k) r).hom ≫
      (linearCoyoneda k (DeckOrbitSkeleton C G)).map f.op := by
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  rfl

namespace CoherentDeckShift

variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

omit [HasShift C (Additive G)]
  [∀ a : Additive G, (shiftFunctor C a).Additive]
  [∀ a : Additive G, (shiftFunctor C a).Linear k] in
set_option backward.isDefEq.respectTransparency false in
/-- Moving projective representables to chosen orbit representatives commutes
with the induced morphism between those representatives. -/
theorem linearCoyonedaMap_objectIsoDeckOrbitRepresentative_naturality
    {X Z : C} (f : X ⟶ Z) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (linearCoyoneda k (ShiftOrbitCategory C (Additive G))).map
        ((ShiftOrbitCategory.identityComponentFunctor
          (C := C) (A := Additive G)).map f).op ≫
      ((linearCoyoneda k
        (ShiftOrbitCategory C (Additive G))).mapIso
          (D.objectIsoDeckOrbitRepresentative X).symm.op).hom =
    ((linearCoyoneda k
      (ShiftOrbitCategory C (Additive G))).mapIso
        (D.objectIsoDeckOrbitRepresentative Z).symm.op).hom ≫
      (linearCoyoneda k (ShiftOrbitCategory C (Additive G))).map
        ((deckOrbitRepresentativeFunctor (C := C) (G := G)).map
          (D.orbitSkeletonMap f)).op := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  change (show ShiftOrbitCategory C (Additive G) from Z) ⟶
    (show ShiftOrbitCategory C (Additive G) from Y) at g
  rw [D.deckOrbitRepresentativeFunctor_map_orbitSkeletonMap]
  change (D.objectIsoDeckOrbitRepresentative X).inv ≫
      ((ShiftOrbitCategory.identityComponentFunctor
        (C := C) (A := Additive G)).map f ≫ g) =
    ((D.objectIsoDeckOrbitRepresentative X).inv ≫
        (ShiftOrbitCategory.identityComponentFunctor
          (C := C) (A := Additive G)).map f ≫
        (D.objectIsoDeckOrbitRepresentative Z).hom) ≫
      ((D.objectIsoDeckOrbitRepresentative Z).inv ≫ g)
  simp [Category.assoc]

/-- Skeletal Gabriel push-down sends the projective representable at `X` to
the projective representable at the strict orbit of `X`. -/
noncomputable def orbitSkeletonPushdownLinearCoyonedaIso (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    orbitSkeletonPushdown (G := G)
        ((linearCoyoneda k C).obj (Opposite.op X)) ≅
      (linearCoyoneda k (DeckOrbitSkeleton C G)).obj
        (Opposite.op
          (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let J := deckOrbitRepresentativeFunctor (C := C) (G := G)
  let q : MulAction.orbitRel.Quotient G C := Quotient.mk'' X
  exact Functor.isoWhiskerLeft J
      (orbitPushdownLinearCoyonedaIso (k := k) (A := Additive G) X) ≪≫
    Functor.isoWhiskerLeft J
      ((linearCoyoneda k (ShiftOrbitCategory C (Additive G))).mapIso
        (D.objectIsoDeckOrbitRepresentative X).symm.op) ≪≫
    deckOrbitRepresentativeLinearCoyonedaIso (k := k) q

omit [HasShift C (Additive G)]
  [∀ a : Additive G, (shiftFunctor C a).Additive]
  [∀ a : Additive G, (shiftFunctor C a).Linear k] in
set_option backward.isDefEq.respectTransparency false in
/-- The skeletal projective-representable isomorphisms commute with the
morphism between strict deck orbits induced by an upstairs morphism. -/
theorem orbitSkeletonPushdownLinearCoyonedaIso_representing_naturality
    {X Z : C} (f : X ⟶ Z) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Functor.whiskerLeft
        (deckOrbitRepresentativeFunctor (C := C) (G := G))
        (orbitPushdownNatTrans (A := Additive G)
          ((linearCoyoneda k C).map f.op)) ≫
      (D.orbitSkeletonPushdownLinearCoyonedaIso (k := k) X).hom =
    (D.orbitSkeletonPushdownLinearCoyonedaIso (k := k) Z).hom ≫
      (linearCoyoneda k (DeckOrbitSkeleton C G)).map
        (D.orbitSkeletonMap f).op := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let J := deckOrbitRepresentativeFunctor (C := C) (G := G)
  let p := Functor.whiskerLeft J
    (orbitPushdownNatTrans (A := Additive G)
      ((linearCoyoneda k C).map f.op))
  let aX := Functor.whiskerLeft J
    (orbitPushdownLinearCoyonedaIso (k := k) (A := Additive G) X).hom
  let aZ := Functor.whiskerLeft J
    (orbitPushdownLinearCoyonedaIso (k := k) (A := Additive G) Z).hom
  let m := Functor.whiskerLeft J
    ((linearCoyoneda k (ShiftOrbitCategory C (Additive G))).map
      ((ShiftOrbitCategory.identityComponentFunctor
        (C := C) (A := Additive G)).map f).op)
  let bX := Functor.whiskerLeft J
    ((linearCoyoneda k
      (ShiftOrbitCategory C (Additive G))).mapIso
        (D.objectIsoDeckOrbitRepresentative X).symm.op).hom
  let bZ := Functor.whiskerLeft J
    ((linearCoyoneda k
      (ShiftOrbitCategory C (Additive G))).mapIso
        (D.objectIsoDeckOrbitRepresentative Z).symm.op).hom
  let n := Functor.whiskerLeft J
    ((linearCoyoneda k (ShiftOrbitCategory C (Additive G))).map
      (J.map (D.orbitSkeletonMap f)).op)
  let cX := (deckOrbitRepresentativeLinearCoyonedaIso
    (k := k) (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)).hom
  let cZ := (deckOrbitRepresentativeLinearCoyonedaIso
    (k := k) (Quotient.mk'' Z : MulAction.orbitRel.Quotient G C)).hom
  let d := (linearCoyoneda k (DeckOrbitSkeleton C G)).map
    (D.orbitSkeletonMap f).op
  change p ≫ aX ≫ bX ≫ cX = (aZ ≫ bZ ≫ cZ) ≫ d
  have h₁ : p ≫ aX = aZ ≫ m := by
    dsimp only [p, aX, aZ, m, J]
    simpa only [Functor.whiskerLeft_comp] using congrArg
      (Functor.whiskerLeft J)
      (orbitPushdownLinearCoyonedaIso_representing_naturality
        (k := k) (A := Additive G) f)
  have h₂ : m ≫ bX = bZ ≫ n := by
    dsimp only [m, bX, bZ, n, J]
    simpa only [Functor.whiskerLeft_comp] using congrArg
      (Functor.whiskerLeft J)
      (D.linearCoyonedaMap_objectIsoDeckOrbitRepresentative_naturality
        (k := k) f)
  have h₃ : n ≫ cX = cZ ≫ d := by
    exact deckOrbitRepresentativeLinearCoyonedaIso_representing_naturality
      (k := k) (D.orbitSkeletonMap f)
  calc
    p ≫ aX ≫ bX ≫ cX = (p ≫ aX) ≫ bX ≫ cX := by
      simp only [Category.assoc]
    _ = (aZ ≫ m) ≫ bX ≫ cX := by rw [h₁]
    _ = aZ ≫ (m ≫ bX) ≫ cX := by simp only [Category.assoc]
    _ = aZ ≫ (bZ ≫ n) ≫ cX := by rw [h₂]
    _ = aZ ≫ bZ ≫ (n ≫ cX) := by simp only [Category.assoc]
    _ = aZ ≫ bZ ≫ (cZ ≫ d) := by rw [h₃]
    _ = (aZ ≫ bZ ≫ cZ) ≫ d := by simp only [Category.assoc]

/-- Bundled linear-module form of skeletal push-down preserving projective
representables. -/
noncomputable def linearModuleOrbitSkeletonPushdownLinearCoyonedaIso (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (linearModuleOrbitSkeletonPushdown
        (k := k) (C := C) (G := G)).obj
        (linearCoyonedaLinearModule (k := k) X) ≅
      linearCoyonedaLinearModule (k := k)
        (C := DeckOrbitSkeleton C G)
        (Quotient.mk'' X : MulAction.orbitRel.Quotient G C) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact (IsLinearModule (C := DeckOrbitSkeleton C G) k).ι.preimageIso
    (D.orbitSkeletonPushdownLinearCoyonedaIso (k := k) X)

omit [HasShift C (Additive G)]
  [∀ a : Additive G, (shiftFunctor C a).Additive]
  [∀ a : Additive G, (shiftFunctor C a).Linear k] in
@[simp]
theorem linearModuleOrbitSkeletonPushdownLinearCoyonedaIso_hom_hom
    (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (D.linearModuleOrbitSkeletonPushdownLinearCoyonedaIso
      (k := k) X).hom.hom =
      (D.orbitSkeletonPushdownLinearCoyonedaIso (k := k) X).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let J := (IsLinearModule.{u, max v w, uK, max v w}
    (C := DeckOrbitSkeleton C G) k).ι
  let LX := (linearModuleOrbitSkeletonPushdown
    (k := k) (C := C) (G := G)).obj
      (linearCoyonedaLinearModule (k := k) X)
  let RX := linearCoyonedaLinearModule (k := k)
    (C := DeckOrbitSkeleton C G)
    (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)
  change (J.preimage (X := LX) (Y := RX)
      (D.orbitSkeletonPushdownLinearCoyonedaIso (k := k) X).hom).hom =
    (D.orbitSkeletonPushdownLinearCoyonedaIso (k := k) X).hom
  exact J.map_preimage (X := LX) (Y := RX)
    (D.orbitSkeletonPushdownLinearCoyonedaIso (k := k) X).hom

omit [HasShift C (Additive G)]
  [∀ a : Additive G, (shiftFunctor C a).Additive]
  [∀ a : Additive G, (shiftFunctor C a).Linear k] in
set_option backward.isDefEq.respectTransparency false in
/-- The skeletal projective comparison is natural in the representing object
inside the category of additive linear modules. -/
theorem linearModuleOrbitSkeletonPushdownLinearCoyonedaIso_representing_naturality
    {X Z : C} (f : X ⟶ Z) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (linearModuleOrbitSkeletonPushdown
        (k := k) (C := C) (G := G)).map
        (linearCoyonedaLinearModuleMap (k := k) f) ≫
      (D.linearModuleOrbitSkeletonPushdownLinearCoyonedaIso
        (k := k) X).hom =
    (D.linearModuleOrbitSkeletonPushdownLinearCoyonedaIso
      (k := k) Z).hom ≫
      linearCoyonedaLinearModuleMap (k := k) (D.orbitSkeletonMap f) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  apply ObjectProperty.hom_ext
  change ((linearModuleOrbitSkeletonPushdown
        (k := k) (C := C) (G := G)).map
        (linearCoyonedaLinearModuleMap (k := k) f)).hom ≫
      (D.linearModuleOrbitSkeletonPushdownLinearCoyonedaIso
        (k := k) X).hom.hom =
    (D.linearModuleOrbitSkeletonPushdownLinearCoyonedaIso
      (k := k) Z).hom.hom ≫
      (linearCoyonedaLinearModuleMap
        (k := k) (D.orbitSkeletonMap f)).hom
  rw [linearModuleOrbitSkeletonPushdownLinearCoyonedaIso_hom_hom,
    linearModuleOrbitSkeletonPushdownLinearCoyonedaIso_hom_hom]
  change Functor.whiskerLeft
        (deckOrbitRepresentativeFunctor (C := C) (G := G))
        (orbitPushdownNatTrans (A := Additive G)
          ((linearCoyoneda k C).map f.op)) ≫
      (D.orbitSkeletonPushdownLinearCoyonedaIso (k := k) X).hom =
    (D.orbitSkeletonPushdownLinearCoyonedaIso (k := k) Z).hom ≫
      (linearCoyoneda k (DeckOrbitSkeleton C G)).map
        (D.orbitSkeletonMap f).op
  exact D.orbitSkeletonPushdownLinearCoyonedaIso_representing_naturality
    (k := k) f

section Finite

variable [IsCancelSMul G C]

/-- The orbit-skeleton representable, with finiteness transported from an
upstairs finite representable through finite skeletal push-down. -/
noncomputable def orbitSkeletonFiniteDimensionalLinearCoyoneda
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    FiniteDimensionalModuleCategory
      (C := DeckOrbitSkeleton C G) k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let MX := finiteDimensionalLinearCoyoneda (k := k) X hX
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  let e := D.linearModuleOrbitSkeletonPushdownLinearCoyonedaIso (k := k) X
  exact ⟨linearCoyonedaLinearModule (k := k)
      (C := DeckOrbitSkeleton C G)
      (Quotient.mk'' X : MulAction.orbitRel.Quotient G C),
    (IsFiniteDimensionalModule (C := DeckOrbitSkeleton C G) k).prop_of_iso
      e (P.obj MX).property⟩

/-- The finite-dimensional skeletal projective representables inherit the map
induced by a morphism of upstairs representing objects. -/
noncomputable def orbitSkeletonFiniteDimensionalLinearCoyonedaMap
    {X Z : C} (f : X ⟶ Z)
    (hX : IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hZ : IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) Z)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    D.orbitSkeletonFiniteDimensionalLinearCoyoneda (k := k) Z hZ ⟶
      D.orbitSkeletonFiniteDimensionalLinearCoyoneda (k := k) X hX := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact ObjectProperty.homMk
    (linearCoyonedaLinearModuleMap (k := k) (D.orbitSkeletonMap f))

/-- Literal finite-dimensional push-down preserves a finite projective
representable. -/
noncomputable def finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
        (finiteDimensionalLinearCoyoneda (k := k) X hX) ≅
      D.orbitSkeletonFiniteDimensionalLinearCoyoneda (k := k) X hX := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact (IsFiniteDimensionalModule (C := DeckOrbitSkeleton C G) k).ι.preimageIso
    (D.linearModuleOrbitSkeletonPushdownLinearCoyonedaIso (k := k) X)

omit [HasShift C (Additive G)]
  [∀ a : Additive G, (shiftFunctor C a).Additive]
  [∀ a : Additive G, (shiftFunctor C a).Linear k] in
@[simp]
theorem finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso_hom_hom
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (D.finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso
      (k := k) X hX).hom.hom =
      (D.linearModuleOrbitSkeletonPushdownLinearCoyonedaIso
        (k := k) X).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let J := (IsFiniteDimensionalModule.{u, max v w, uK, max v w}
    (C := DeckOrbitSkeleton C G) k).ι
  let LX := (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
    (finiteDimensionalLinearCoyoneda (k := k) X hX)
  let RX := D.orbitSkeletonFiniteDimensionalLinearCoyoneda
    (k := k) X hX
  change (J.preimage (X := LX) (Y := RX)
      (D.linearModuleOrbitSkeletonPushdownLinearCoyonedaIso
        (k := k) X).hom).hom =
    (D.linearModuleOrbitSkeletonPushdownLinearCoyonedaIso
      (k := k) X).hom
  exact J.map_preimage (X := LX) (Y := RX)
    (D.linearModuleOrbitSkeletonPushdownLinearCoyonedaIso
      (k := k) X).hom

omit [HasShift C (Additive G)]
  [∀ a : Additive G, (shiftFunctor C a).Additive]
  [∀ a : Additive G, (shiftFunctor C a).Linear k] in
set_option backward.isDefEq.respectTransparency false in
/-- Literal finite-dimensional skeletal push-down preserves the morphisms
between finite projective representables. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso_representing_naturality
    {X Z : C} (f : X ⟶ Z)
    (hX : IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hZ : IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) Z)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map
        (finiteDimensionalLinearCoyonedaMap (k := k) f hX hZ) ≫
      (D.finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso
        (k := k) X hX).hom =
    (D.finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso
      (k := k) Z hZ).hom ≫
      D.orbitSkeletonFiniteDimensionalLinearCoyonedaMap
        (k := k) f hX hZ := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  apply ObjectProperty.hom_ext
  change ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map
        (finiteDimensionalLinearCoyonedaMap (k := k) f hX hZ)).hom ≫
      (D.finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso
        (k := k) X hX).hom.hom =
    (D.finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso
      (k := k) Z hZ).hom.hom ≫
      (D.orbitSkeletonFiniteDimensionalLinearCoyonedaMap
        (k := k) f hX hZ).hom
  rw [finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso_hom_hom,
    finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso_hom_hom]
  exact D.linearModuleOrbitSkeletonPushdownLinearCoyonedaIso_representing_naturality
    (k := k) f

end Finite

end CoherentDeckShift

end OrbitSkeleton

end MagnitudeConjecture.CoveringHom
