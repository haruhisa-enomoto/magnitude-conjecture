import MagnitudeConjecture.CategoryTheory.FiniteMeshEndLocal
import MagnitudeConjecture.CategoryTheory.LinearPathCovering
import MagnitudeConjecture.CategoryTheory.MeshRealization
import MagnitudeConjecture.CategoryTheory.TranslationQuiverPeriodicComponent
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Mesh categories of periodic stable components

The mesh relation of an induced periodic component is obtained from the
ambient mesh relation by killing every path through a vertex outside the
component.  We realize this deletion concretely in the presheaf category of
the component mesh: component vertices go to their linear Yoneda
representables, while outside vertices go to the zero presheaf.

This supplies a surjection from each ambient mesh Hom space between component
vertices onto the corresponding component mesh Hom space.  In particular,
Hom-finiteness descends from a finite ambient mesh to each periodic component.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open ZeroObject

namespace MagnitudeConjecture.MeshCategory.RightMeshData.IsTauInjective

universe u v

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{v} Q]
variable [∀ x : Q, Fintype (Σ y : Q, x ⟶ y)]
variable (T : RightMeshData Q) (hT : T.IsTauInjective)

/-- Outgoing stars in the full induced component quiver are the subtype of
ambient stars whose terminal vertex remains in the component. -/
def periodicComponentStarEquiv
    (E : PeriodicComponent T hT)
    (x : PeriodicComponentVertex T hT E) :
    (Σ y : PeriodicComponentVertex T hT E, x ⟶ y) ≃
      {a : Σ y : Q, x.1 ⟶ y // IsInPeriodicComponent T hT E a.1} where
  toFun a := ⟨⟨a.1.1, a.2⟩, a.1.2⟩
  invFun a := ⟨⟨a.1.1, a.2⟩, a.1.2⟩
  left_inv a := by
    rcases a with ⟨y, a⟩
    rfl
  right_inv a := by
    rcases a with ⟨⟨y, a⟩, hy⟩
    rfl

noncomputable instance periodicComponentStarFintype
    (E : PeriodicComponent T hT)
    (x : PeriodicComponentVertex T hT E) :
    Fintype (Σ y : PeriodicComponentVertex T hT E, x ⟶ y) := by
  classical
  exact Fintype.ofEquiv
    {a : Σ y : Q, x.1 ⟶ y // IsInPeriodicComponent T hT E a.1}
    (periodicComponentStarEquiv T hT E x).symm

/-- The raw mesh category of one induced periodic component. -/
abbrev PeriodicComponentMeshCategory
    (k : Type u) [Field k]
    (E : PeriodicComponent T hT) :=
  RawCategory (k := k) (periodicComponentRightMeshData T hT E)

/-- A component vertex as an object of its raw mesh category. -/
abbrev periodicComponentMeshObj
    {E : PeriodicComponent T hT}
    (x : PeriodicComponentVertex T hT E) :
    PeriodicComponentMeshCategory T hT k E :=
  obj (k := k) (periodicComponentRightMeshData T hT E) x

/-- The component-mesh morphism represented by one component arrow. -/
def periodicComponentPathHom
    {E : PeriodicComponent T hT}
    {x y : PeriodicComponentVertex T hT E} (p : Quiver.Path x y) :
    MagnitudeConjecture.LinearPathCategory.obj k
          (PeriodicComponentVertex T hT E) y ⟶
      MagnitudeConjecture.LinearPathCategory.obj k
          (PeriodicComponentVertex T hT E) x :=
  MagnitudeConjecture.LinearPathCategory.pathHom (k := k) p

/-- The component-mesh morphism represented by one component arrow. -/
def periodicComponentArrowHom
    {E : PeriodicComponent T hT}
    {x y : PeriodicComponentVertex T hT E} (a : x ⟶ y) :
  periodicComponentMeshObj (k := k) T hT y ⟶
      periodicComponentMeshObj (k := k) T hT x :=
  (quotientFunctor (k := k) (periodicComponentRightMeshData T hT E)).map
    (periodicComponentPathHom (k := k) T hT a.toPath)

omit [∀ x : Q, Fintype (Σ y : Q, x ⟶ y)] in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem periodicComponentPathHom_nil
    {E : PeriodicComponent T hT}
    (x : PeriodicComponentVertex T hT E) :
    periodicComponentPathHom (k := k) T hT
        (Quiver.Path.nil : Quiver.Path x x) =
      𝟙 (MagnitudeConjecture.LinearPathCategory.obj k
        (PeriodicComponentVertex T hT E) x) := by
  exact MagnitudeConjecture.LinearPathCategory.pathHom_nil _

omit [∀ x : Q, Fintype (Σ y : Q, x ⟶ y)] in
set_option backward.isDefEq.respectTransparency false in
/-- In the reversed free path category, adjoining the final component arrow
is composition on the left. -/
theorem periodicComponentPathHom_cons
    {E : PeriodicComponent T hT}
    {x y z : PeriodicComponentVertex T hT E}
    (p : Quiver.Path x y) (a : y ⟶ z) :
    periodicComponentPathHom (k := k) T hT a.toPath ≫
        periodicComponentPathHom (k := k) T hT p =
      periodicComponentPathHom (k := k) T hT (p.cons a) := by
  exact MagnitudeConjecture.LinearPathCategory.pathHom_comp a.toPath p

/-- The same path-composition identity after quotienting by the component
mesh relations. -/
theorem periodicComponentArrowHom_comp_pathHom
    {E : PeriodicComponent T hT}
    {x y z : PeriodicComponentVertex T hT E}
    (p : Quiver.Path x y) (a : y ⟶ z) :
    periodicComponentArrowHom (k := k) T hT a ≫
        (quotientFunctor (k := k)
          (periodicComponentRightMeshData T hT E)).map
            (periodicComponentPathHom (k := k) T hT p) =
      (quotientFunctor (k := k)
        (periodicComponentRightMeshData T hT E)).map
          (periodicComponentPathHom (k := k) T hT (p.cons a)) := by
  unfold periodicComponentArrowHom
  rw [← (quotientFunctor (k := k)
    (periodicComponentRightMeshData T hT E)).map_comp]
  rw [periodicComponentPathHom_cons]

/-- Target category used to kill ambient vertices outside a chosen component. -/
abbrev PeriodicComponentPresheafCategory
    (k : Type u) [Field k]
    (E : PeriodicComponent T hT) :=
  (PeriodicComponentMeshCategory T hT k E)ᵒᵖ ⥤ ModuleCat k

noncomputable local instance periodicComponentLinearYonedaAdditive
    (E : PeriodicComponent T hT) :
    (CategoryTheory.linearYoneda k
      (PeriodicComponentMeshCategory T hT k E)).Additive where
  map_add := by
    intro X Y f g
    ext Z z
    change z ≫ (f + g) = z ≫ f + z ≫ g
    exact Preadditive.comp_add Z.unop X Y z f g

noncomputable local instance periodicComponentLinearYonedaLinear
    (E : PeriodicComponent T hT) :
    (CategoryTheory.linearYoneda k
      (PeriodicComponentMeshCategory T hT k E)).Linear k where
  map_smul := by
    intro X Y f r
    ext Z z
    change z ≫ (r • f) = r • (z ≫ f)
    exact CategoryTheory.Linear.comp_smul Z.unop X Y z r f

/-- An ambient vertex is sent to its component-mesh representable when it
belongs to the chosen component and to the zero presheaf otherwise. -/
def ambientComponentYonedaObj
    (E : PeriodicComponent T hT) (x : Q) :
    PeriodicComponentPresheafCategory T hT k E := by
  classical
  exact if hx : IsInPeriodicComponent T hT E x then
      (CategoryTheory.linearYoneda k
      (PeriodicComponentMeshCategory T hT k E)).obj
        (periodicComponentMeshObj (k := k) T hT ⟨x, hx⟩)
  else 0

@[simp]
theorem ambientComponentYonedaObj_of_mem
    (E : PeriodicComponent T hT) {x : Q}
    (hx : IsInPeriodicComponent T hT E x) :
    ambientComponentYonedaObj (k := k) T hT E x =
      (CategoryTheory.linearYoneda k
        (PeriodicComponentMeshCategory T hT k E)).obj
          (periodicComponentMeshObj (k := k) T hT ⟨x, hx⟩) := by
  simp [ambientComponentYonedaObj, hx]

@[simp]
theorem ambientComponentYonedaObj_of_not_mem
    (E : PeriodicComponent T hT) {x : Q}
    (hx : ¬ IsInPeriodicComponent T hT E x) :
    ambientComponentYonedaObj (k := k) T hT E x = 0 := by
  simp [ambientComponentYonedaObj, hx]

/-- The canonical object identification attached to a component vertex.  By
using the vertex itself, rather than reconstructing its subtype witness from
an ambient endpoint, path-composition transports share literally the same
middle equality. -/
theorem ambientComponentYonedaObjEq
    (E : PeriodicComponent T hT)
    (x : PeriodicComponentVertex T hT E) :
    ambientComponentYonedaObj (k := k) T hT E x.1 =
      (CategoryTheory.linearYoneda k
        (PeriodicComponentMeshCategory T hT k E)).obj
          (periodicComponentMeshObj (k := k) T hT x) :=
  ambientComponentYonedaObj_of_mem (k := k) T hT E x.2

/-- Ambient arrows internal to the component act by linear Yoneda; every
arrow incident with an outside vertex acts by zero. -/
def ambientComponentYonedaArrow
    (E : PeriodicComponent T hT) {x y : Q} (a : x ⟶ y) :
    ambientComponentYonedaObj (k := k) T hT E y ⟶
      ambientComponentYonedaObj (k := k) T hT E x := by
  classical
  by_cases hx : IsInPeriodicComponent T hT E x
  · by_cases hy : IsInPeriodicComponent T hT E y
    · exact
        eqToHom (ambientComponentYonedaObj_of_mem (k := k) T hT E hy) ≫
          (CategoryTheory.linearYoneda k
            (PeriodicComponentMeshCategory T hT k E)).map
              (periodicComponentArrowHom (k := k) T hT
                (show (⟨x, hx⟩ : PeriodicComponentVertex T hT E) ⟶
                    (⟨y, hy⟩ : PeriodicComponentVertex T hT E) from a)) ≫
            eqToHom
              (ambientComponentYonedaObj_of_mem (k := k) T hT E hx).symm
    · rw [ambientComponentYonedaObj_of_not_mem T hT E hy]
      exact 0
  · rw [ambientComponentYonedaObj_of_not_mem T hT E hx]
    exact 0

/-- After transporting the two object identifications, an internal ambient
arrow is exactly the Yoneda image of its component arrow. -/
theorem ambientComponentYonedaArrow_of_mem
    (E : PeriodicComponent T hT) {x y : Q} (a : x ⟶ y)
    (hx : IsInPeriodicComponent T hT E x)
    (hy : IsInPeriodicComponent T hT E y) :
    eqToHom (ambientComponentYonedaObj_of_mem (k := k) T hT E hy).symm ≫
        ambientComponentYonedaArrow (k := k) T hT E a ≫
          eqToHom (ambientComponentYonedaObj_of_mem (k := k) T hT E hx) =
      (CategoryTheory.linearYoneda k
        (PeriodicComponentMeshCategory T hT k E)).map
          (periodicComponentArrowHom (k := k) T hT
            (show (⟨x, hx⟩ : PeriodicComponentVertex T hT E) ⟶
                (⟨y, hy⟩ : PeriodicComponentVertex T hT E) from a)) := by
  classical
  simp [ambientComponentYonedaArrow, hx, hy]

/-- Before transporting endpoints, an internal ambient arrow is the Yoneda
image of the corresponding component arrow conjugated by the two canonical
object identifications. -/
theorem ambientComponentYonedaArrow_eq_of_mem
    (E : PeriodicComponent T hT) {x y : Q} (a : x ⟶ y)
    (hx : IsInPeriodicComponent T hT E x)
    (hy : IsInPeriodicComponent T hT E y) :
    ambientComponentYonedaArrow (k := k) T hT E a =
      eqToHom (ambientComponentYonedaObj_of_mem (k := k) T hT E hy) ≫
        (CategoryTheory.linearYoneda k
          (PeriodicComponentMeshCategory T hT k E)).map
            (periodicComponentArrowHom (k := k) T hT
              (show (⟨x, hx⟩ : PeriodicComponentVertex T hT E) ⟶
                  (⟨y, hy⟩ : PeriodicComponentVertex T hT E) from a)) ≫
          eqToHom
            (ambientComponentYonedaObj_of_mem (k := k) T hT E hx).symm := by
  classical
  simp [ambientComponentYonedaArrow, hx, hy]

@[simp]
theorem ambientComponentYonedaArrow_of_not_mem_source
    (E : PeriodicComponent T hT) {x y : Q} (a : x ⟶ y)
    (hx : ¬ IsInPeriodicComponent T hT E x) :
    ambientComponentYonedaArrow (k := k) T hT E a = 0 := by
  classical
  simp [ambientComponentYonedaArrow, hx]

@[simp]
theorem ambientComponentYonedaArrow_of_not_mem_target
    (E : PeriodicComponent T hT) {x y : Q} (a : x ⟶ y)
    (hy : ¬ IsInPeriodicComponent T hT E y) :
    ambientComponentYonedaArrow (k := k) T hT E a = 0 := by
  classical
  by_cases hx : IsInPeriodicComponent T hT E x
  · simp [ambientComponentYonedaArrow, hx, hy]
  · simp [ambientComponentYonedaArrow, hx]

/-- The image of one ambient mesh summand under the zero-extended Yoneda
assignment. -/
def ambientComponentMeshTerm
    (E : PeriodicComponent T hT)
    (x : {x : Q // x ∉ T.projective}) (a : T.MeshArrow x) :
    ambientComponentYonedaObj (k := k) T hT E (T.tau x) ⟶
      ambientComponentYonedaObj (k := k) T hT E x.1 :=
  ambientComponentYonedaArrow (k := k) T hT E
      (T.arrowEquiv x a.1 a.2) ≫
    ambientComponentYonedaArrow (k := k) T hT E a.2

@[simp]
theorem ambientComponentMeshTerm_of_not_mem_source
    (E : PeriodicComponent T hT)
    (x : {x : Q // x ∉ T.projective}) (a : T.MeshArrow x)
    (hx : ¬ IsInPeriodicComponent T hT E x.1) :
    ambientComponentMeshTerm (k := k) T hT E x a = 0 := by
  simp [ambientComponentMeshTerm,
    ambientComponentYonedaArrow_of_not_mem_source T hT E a.2 hx]

@[simp]
theorem ambientComponentMeshTerm_of_not_mem_middle
    (E : PeriodicComponent T hT)
    (x : {x : Q // x ∉ T.projective}) (a : T.MeshArrow x)
    (hy : ¬ IsInPeriodicComponent T hT E a.1) :
    ambientComponentMeshTerm (k := k) T hT E x a = 0 := by
  simp [ambientComponentMeshTerm,
    ambientComponentYonedaArrow_of_not_mem_source T hT E
      (T.arrowEquiv x a.1 a.2) hy]

/-- An internal ambient mesh summand, transported to component
representables, is the Yoneda image of the corresponding component mesh
path. -/
theorem transported_ambientComponentMeshTerm_of_mem
    (E : PeriodicComponent T hT)
    (x : {x : Q // x ∉ T.projective}) (a : T.MeshArrow x)
    (hx : IsInPeriodicComponent T hT E x.1)
    (hy : IsInPeriodicComponent T hT E a.1) :
    let xc : PeriodicComponentVertex T hT E := ⟨x.1, hx⟩
    let sx : {z : PeriodicComponentVertex T hT E //
        z ∉ (periodicComponentRightMeshData T hT E).projective} :=
      ⟨xc, by simp⟩
    let tc : PeriodicComponentVertex T hT E :=
      (periodicComponentRightMeshData T hT E).tau sx
    let b : (periodicComponentRightMeshData T hT E).MeshArrow sx :=
      ⟨⟨a.1, hy⟩, a.2⟩
    let htau : IsInPeriodicComponent T hT E (T.tau x) :=
      tc.2
    eqToHom
          (ambientComponentYonedaObj_of_mem (k := k) T hT E htau).symm ≫
        ambientComponentMeshTerm (k := k) T hT E x a ≫
          eqToHom (ambientComponentYonedaObj_of_mem (k := k) T hT E hx) =
      (CategoryTheory.linearYoneda k
        (PeriodicComponentMeshCategory T hT k E)).map
          ((quotientFunctor (k := k)
            (periodicComponentRightMeshData T hT E)).map
              (MagnitudeConjecture.LinearPathCategory.pathHom (k := k)
                ((periodicComponentRightMeshData T hT E).meshPath sx b))) := by
  classical
  dsimp only
  let xc : PeriodicComponentVertex T hT E := ⟨x.1, hx⟩
  let yc : PeriodicComponentVertex T hT E := ⟨a.1, hy⟩
  let sx : {z : PeriodicComponentVertex T hT E //
      z ∉ (periodicComponentRightMeshData T hT E).projective} :=
    ⟨xc, by simp⟩
  let tc : PeriodicComponentVertex T hT E :=
    (periodicComponentRightMeshData T hT E).tau sx
  let b : (periodicComponentRightMeshData T hT E).MeshArrow sx :=
    ⟨yc, a.2⟩
  let partner : yc ⟶ tc :=
    (periodicComponentRightMeshData T hT E).arrowEquiv sx yc a.2
  let eX : ambientComponentYonedaObj (k := k) T hT E x.1 =
      (CategoryTheory.linearYoneda k
        (PeriodicComponentMeshCategory T hT k E)).obj
          (periodicComponentMeshObj (k := k) T hT xc) :=
    ambientComponentYonedaObj_of_mem (k := k) T hT E hx
  let eY : ambientComponentYonedaObj (k := k) T hT E a.1 =
      (CategoryTheory.linearYoneda k
        (PeriodicComponentMeshCategory T hT k E)).obj
          (periodicComponentMeshObj (k := k) T hT yc) :=
    ambientComponentYonedaObj_of_mem (k := k) T hT E hy
  let eT : ambientComponentYonedaObj (k := k) T hT E (T.tau x) =
      (CategoryTheory.linearYoneda k
        (PeriodicComponentMeshCategory T hT k E)).obj
          (periodicComponentMeshObj (k := k) T hT tc) :=
    ambientComponentYonedaObj_of_mem (k := k) T hT E tc.2
  have hpartner :
      (show a.1 ⟶ T.tau x from T.arrowEquiv x a.1 a.2) = partner := by
    rfl
  have hmapPartner := congrArg
    (fun q : a.1 ⟶ T.tau x ↦
      ambientComponentYonedaArrow (k := k) T hT E q) hpartner
  have ha :
      eqToHom eY.symm ≫
          ambientComponentYonedaArrow (k := k) T hT E a.2 ≫
        eqToHom eX =
      (CategoryTheory.linearYoneda k
        (PeriodicComponentMeshCategory T hT k E)).map
          (periodicComponentArrowHom (k := k) T hT
            (show xc ⟶ yc from a.2)) :=
    ambientComponentYonedaArrow_of_mem (k := k) T hT E a.2 hx hy
  have hp :
      eqToHom eT.symm ≫
          ambientComponentYonedaArrow (k := k) T hT E partner ≫
        eqToHom eY =
      (CategoryTheory.linearYoneda k
        (PeriodicComponentMeshCategory T hT k E)).map
          (periodicComponentArrowHom (k := k) T hT partner) :=
    ambientComponentYonedaArrow_of_mem (k := k) T hT E partner hy tc.2
  have htermPartner := congrArg
    (fun f ↦
      eqToHom eT.symm ≫
        (f ≫ ambientComponentYonedaArrow (k := k) T hT E a.2) ≫
          eqToHom eX)
    hmapPartner
  change
    eqToHom eT.symm ≫
        (ambientComponentYonedaArrow (k := k) T hT E
            (T.arrowEquiv x a.1 a.2) ≫
          ambientComponentYonedaArrow (k := k) T hT E a.2) ≫
          eqToHom eX = _
  calc
    _ =
        (eqToHom eT.symm ≫
            ambientComponentYonedaArrow (k := k) T hT E
              partner ≫
            eqToHom eY) ≫
          (eqToHom eY.symm ≫
            ambientComponentYonedaArrow (k := k) T hT E a.2 ≫
            eqToHom eX) := by
          exact htermPartner.trans (by simp [Category.assoc])
    _ =
        (CategoryTheory.linearYoneda k
            (PeriodicComponentMeshCategory T hT k E)).map
              (periodicComponentArrowHom (k := k) T hT
                partner) ≫
          (CategoryTheory.linearYoneda k
            (PeriodicComponentMeshCategory T hT k E)).map
              (periodicComponentArrowHom (k := k) T hT
                (show xc ⟶ yc from a.2)) := by
          rw [hp, ha]
    _ =
        (CategoryTheory.linearYoneda k
          (PeriodicComponentMeshCategory T hT k E)).map
            ((periodicComponentArrowHom (k := k) T hT
                partner) ≫
              periodicComponentArrowHom (k := k) T hT
                (show xc ⟶ yc from a.2)) := by
          rw [← Functor.map_comp]
    _ = _ := by
      unfold periodicComponentArrowHom
      rw [← (quotientFunctor (k := k)
        (periodicComponentRightMeshData T hT E)).map_comp]
      rw [periodicComponentPathHom_cons]
      rfl

/-- Evaluating an ambient mesh relation under the zero-extended arrow
assignment gives the sum of the displayed ambient mesh terms. -/
theorem ambientComponentYonedaLift_map_meshRelation
    (E : PeriodicComponent T hT)
    (x : {x : Q // x ∉ T.projective}) :
    (MagnitudeConjecture.LinearPathCategory.lift
        (k := k) (ambientComponentYonedaObj (k := k) T hT E)
          (ambientComponentYonedaArrow (k := k) T hT E)).map
        (T.meshRelation (k := k) x) =
      ∑ a : T.MeshArrow x,
        ambientComponentMeshTerm (k := k) T hT E x a := by
  classical
  rw [RightMeshData.meshRelation, Functor.map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [MagnitudeConjecture.LinearPathCategory.lift_map_pathHom]
  change MagnitudeConjecture.LinearPathCategory.pathMap
      (ambientComponentYonedaObj (k := k) T hT E)
      (ambientComponentYonedaArrow (k := k) T hT E)
      ((Quiver.Path.nil.cons a.2).cons (T.arrowEquiv x a.1 a.2)) = _
  rw [MagnitudeConjecture.LinearPathCategory.pathMap_cons,
    MagnitudeConjecture.LinearPathCategory.pathMap_cons,
    MagnitudeConjecture.LinearPathCategory.pathMap_nil,
    Category.comp_id]
  rfl

/-- Every ambient mesh relation vanishes under the zero-extended component
Yoneda assignment. -/
theorem ambientComponentYonedaLift_map_meshRelation_eq_zero
    (E : PeriodicComponent T hT)
    (x : {x : Q // x ∉ T.projective}) :
    (MagnitudeConjecture.LinearPathCategory.lift
        (k := k) (ambientComponentYonedaObj (k := k) T hT E)
          (ambientComponentYonedaArrow (k := k) T hT E)).map
        (T.meshRelation (k := k) x) = 0 := by
  classical
  rw [ambientComponentYonedaLift_map_meshRelation (k := k) T hT E x]
  by_cases hx : IsInPeriodicComponent T hT E x.1
  · let xc : PeriodicComponentVertex T hT E := ⟨x.1, hx⟩
    let sx : {z : PeriodicComponentVertex T hT E //
        z ∉ (periodicComponentRightMeshData T hT E).projective} :=
      ⟨xc, by simp⟩
    let tc : PeriodicComponentVertex T hT E :=
      (periodicComponentRightMeshData T hT E).tau sx
    let eX : ambientComponentYonedaObj (k := k) T hT E x.1 =
        (CategoryTheory.linearYoneda k
          (PeriodicComponentMeshCategory T hT k E)).obj
            (periodicComponentMeshObj (k := k) T hT xc) :=
      ambientComponentYonedaObj_of_mem (k := k) T hT E hx
    let eT : ambientComponentYonedaObj (k := k) T hT E (T.tau x) =
        (CategoryTheory.linearYoneda k
          (PeriodicComponentMeshCategory T hT k E)).obj
            (periodicComponentMeshObj (k := k) T hT tc) :=
      ambientComponentYonedaObj_of_mem (k := k) T hT E tc.2
    let Y := CategoryTheory.linearYoneda k
      (PeriodicComponentMeshCategory T hT k E)
    let f (a : T.MeshArrow x) :
        Y.obj (periodicComponentMeshObj (k := k) T hT tc) ⟶
          Y.obj (periodicComponentMeshObj (k := k) T hT xc) :=
      eqToHom eT.symm ≫
        ambientComponentMeshTerm (k := k) T hT E x a ≫
          eqToHom eX
    let g (b : (periodicComponentRightMeshData T hT E).MeshArrow sx) :
        Y.obj (periodicComponentMeshObj (k := k) T hT tc) ⟶
          Y.obj (periodicComponentMeshObj (k := k) T hT xc) :=
      Y.map
        ((quotientFunctor (k := k)
          (periodicComponentRightMeshData T hT E)).map
            (MagnitudeConjecture.LinearPathCategory.pathHom (k := k)
              ((periodicComponentRightMeshData T hT E).meshPath sx b)))
    let p : T.MeshArrow x → Prop := fun a ↦
      IsInPeriodicComponent T hT E a.1
    let e := periodicComponentMeshArrowEquiv T hT E sx
    have hinternal (a : {a : T.MeshArrow x // p a}) :
        f a.1 = g (e.symm a) := by
      simp only [f, g, p, e]
      convert
        (transported_ambientComponentMeshTerm_of_mem
          (k := k) T hT E x a.1 hx a.2) using 1
      all_goals rfl
    have hexternal (a : {a : T.MeshArrow x // ¬ p a}) :
        f a.1 = 0 := by
      dsimp only [f, p]
      rw [ambientComponentMeshTerm_of_not_mem_middle
        (k := k) T hT E x a.1 a.2]
      simp
    have hpartition := Fintype.sum_subtype_add_sum_subtype p f
    have hexternalSum : ∑ a : {a : T.MeshArrow x // ¬ p a}, f a.1 = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      exact hexternal a
    have hfullInternal :
        (∑ a : T.MeshArrow x, f a) =
          ∑ a : {a : T.MeshArrow x // p a}, f a.1 := by
      rw [hexternalSum, add_zero] at hpartition
      exact hpartition.symm
    have hreindex :
        (∑ a : {a : T.MeshArrow x // p a}, g (e.symm a)) =
          ∑ b : (periodicComponentRightMeshData T hT E).MeshArrow sx, g b :=
      e.symm.sum_comp g
    have hcomponentSum :
        (∑ b : (periodicComponentRightMeshData T hT E).MeshArrow sx, g b) = 0 := by
      change
        (∑ b : (periodicComponentRightMeshData T hT E).MeshArrow sx,
          Y.map
            ((quotientFunctor (k := k)
              (periodicComponentRightMeshData T hT E)).map
                (MagnitudeConjecture.LinearPathCategory.pathHom (k := k)
                  ((periodicComponentRightMeshData T hT E).meshPath sx b)))) = 0
      rw [← Functor.map_sum, ← Functor.map_sum]
      change
        Y.map
          ((quotientFunctor (k := k)
            (periodicComponentRightMeshData T hT E)).map
              ((periodicComponentRightMeshData T hT E).meshRelation
                (k := k) sx)) = 0
      rw [quotient_map_meshRelation_eq_zero]
      exact Y.map_zero _ _
    have hsumF : (∑ a : T.MeshArrow x, f a) = 0 := by
      rw [hfullInternal]
      calc
        (∑ a : {a : T.MeshArrow x // p a}, f a.1) =
            ∑ a : {a : T.MeshArrow x // p a}, g (e.symm a) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hinternal a
        _ = ∑ b : (periodicComponentRightMeshData T hT E).MeshArrow sx, g b :=
          hreindex
        _ = 0 := hcomponentSum
    have htransport :
        eqToHom eT.symm ≫
            (∑ a : T.MeshArrow x,
              ambientComponentMeshTerm (k := k) T hT E x a) ≫
          eqToHom eX = 0 := by
      have hdistribute (s : Finset (T.MeshArrow x)) :
          eqToHom eT.symm ≫
                s.sum (fun a ↦
                  ambientComponentMeshTerm (k := k) T hT E x a) ≫
              eqToHom eX =
            s.sum f := by
        induction s using Finset.induction_on with
        | empty => simp
        | @insert a s ha ih =>
            rw [Finset.sum_insert ha, Finset.sum_insert ha]
            rw [Preadditive.add_comp, Preadditive.comp_add, ih]
      calc
        eqToHom eT.symm ≫
              (∑ a : T.MeshArrow x,
                ambientComponentMeshTerm (k := k) T hT E x a) ≫
            eqToHom eX =
            ∑ a : T.MeshArrow x, f a := by
              simpa using hdistribute Finset.univ
        _ = 0 := hsumF
    have hback := congrArg
      (fun q ↦ eqToHom eT ≫ q ≫ eqToHom eX.symm) htransport
    change
      (∑ a : T.MeshArrow x,
        ambientComponentMeshTerm (k := k) T hT E x a) = 0
    simpa [Category.assoc] using hback
  · apply Finset.sum_eq_zero
    intro a ha
    exact ambientComponentMeshTerm_of_not_mem_source
      (k := k) T hT E x a hx

/-- The ambient mesh realization which retains one periodic component and
kills all other vertices. -/
def ambientComponentYonedaRealization
    (E : PeriodicComponent T hT) :
    Realization (k := k) T
      (ambientComponentYonedaObj (k := k) T hT E) where
  arrowMap := ambientComponentYonedaArrow (k := k) T hT E
  map_meshRelation :=
    ambientComponentYonedaLift_map_meshRelation_eq_zero (k := k) T hT E

/-- The arrow formula specialized to an arrow of the induced component
quiver. -/
theorem ambientComponentYonedaArrow_inclusion
    (E : PeriodicComponent T hT)
    {x y : PeriodicComponentVertex T hT E} (a : x ⟶ y) :
    ambientComponentYonedaArrow (k := k) T hT E
        ((periodicComponentInclusion T hT E).map a) =
      eqToHom (ambientComponentYonedaObjEq (k := k) T hT E y) ≫
        (CategoryTheory.linearYoneda k
          (PeriodicComponentMeshCategory T hT k E)).map
            (periodicComponentArrowHom (k := k) T hT a) ≫
          eqToHom
            (ambientComponentYonedaObjEq (k := k) T hT E x).symm := by
  classical
  simp [ambientComponentYonedaArrow, x.2, y.2,
    periodicComponentInclusion_map]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating an included component path in the ambient realization gives
the Yoneda image of the same path in the component mesh category, conjugated
by the canonical endpoint identifications. -/
theorem ambientComponentYoneda_pathMap_inclusion
    (E : PeriodicComponent T hT)
    {x y : PeriodicComponentVertex T hT E} (p : Quiver.Path x y) :
    MagnitudeConjecture.LinearPathCategory.pathMap
        (ambientComponentYonedaObj (k := k) T hT E)
        (ambientComponentYonedaArrow (k := k) T hT E)
        ((periodicComponentInclusion T hT E).mapPath p) =
      eqToHom (ambientComponentYonedaObjEq (k := k) T hT E y) ≫
        (CategoryTheory.linearYoneda k
          (PeriodicComponentMeshCategory T hT k E)).map
            ((quotientFunctor (k := k)
              (periodicComponentRightMeshData T hT E)).map
                (periodicComponentPathHom (k := k) T hT p)) ≫
          eqToHom
            (ambientComponentYonedaObjEq (k := k) T hT E x).symm := by
  classical
  induction p with
  | nil =>
      rw [Prefunctor.mapPath_nil,
        MagnitudeConjecture.LinearPathCategory.pathMap_nil,
        periodicComponentPathHom_nil,
        (quotientFunctor (k := k)
          (periodicComponentRightMeshData T hT E)).map_id,
        (CategoryTheory.linearYoneda k
          (PeriodicComponentMeshCategory T hT k E)).map_id]
      simp
  | @cons b c p a ih =>
      rw [Prefunctor.mapPath_cons,
        MagnitudeConjecture.LinearPathCategory.pathMap_cons]
      simp only [periodicComponentInclusion_obj] at ih ⊢
      rw [
        ambientComponentYonedaArrow_inclusion
          (k := k) T hT E a,
        ih]
      simp only [Category.assoc]
      have hcancel :
          eqToHom (ambientComponentYonedaObjEq (k := k) T hT E b).symm ≫
              eqToHom (ambientComponentYonedaObjEq (k := k) T hT E b) =
            𝟙 _ := by simp
      rw [← Category.assoc
        (eqToHom (ambientComponentYonedaObjEq (k := k) T hT E b).symm)
        (eqToHom (ambientComponentYonedaObjEq (k := k) T hT E b)),
        hcancel, Category.id_comp]
      rw [← Functor.map_comp_assoc]
      rw [periodicComponentArrowHom_comp_pathHom]

set_option backward.isDefEq.respectTransparency false in
/-- The path calculation extended linearly to every component free-path
morphism. -/
theorem ambientComponentYoneda_freeFunctor_map_inclusion
    (E : PeriodicComponent T hT)
    {x y : PeriodicComponentVertex T hT E}
    (f : MagnitudeConjecture.LinearPathCategory.obj k
            (PeriodicComponentVertex T hT E) y ⟶
          MagnitudeConjecture.LinearPathCategory.obj k
            (PeriodicComponentVertex T hT E) x) :
    (ambientComponentYonedaRealization (k := k) T hT E).freeFunctor.map
        ((MagnitudeConjecture.LinearPathCategory.prefunctorFunctor
          (k := k) (periodicComponentInclusion T hT E)).map f) =
      eqToHom (ambientComponentYonedaObjEq (k := k) T hT E y) ≫
        (CategoryTheory.linearYoneda k
          (PeriodicComponentMeshCategory T hT k E)).map
            ((quotientFunctor (k := k)
              (periodicComponentRightMeshData T hT E)).map f) ≫
          eqToHom
            (ambientComponentYonedaObjEq (k := k) T hT E x).symm := by
  classical
  let f' := MagnitudeConjecture.LinearPathCategory.homPathLinearEquiv
    (MagnitudeConjecture.LinearPathCategory.obj k
      (PeriodicComponentVertex T hT E) y)
    (MagnitudeConjecture.LinearPathCategory.obj k
      (PeriodicComponentVertex T hT E) x) f
  rw [← (MagnitudeConjecture.LinearPathCategory.homPathLinearEquiv
    (MagnitudeConjecture.LinearPathCategory.obj k
      (PeriodicComponentVertex T hT E) y)
    (MagnitudeConjecture.LinearPathCategory.obj k
      (PeriodicComponentVertex T hT E) x)).symm_apply_apply f]
  change
    (ambientComponentYonedaRealization (k := k) T hT E).freeFunctor.map
        ((MagnitudeConjecture.LinearPathCategory.prefunctorFunctor
          (k := k) (periodicComponentInclusion T hT E)).map
            ((MagnitudeConjecture.LinearPathCategory.homPathLinearEquiv
              (MagnitudeConjecture.LinearPathCategory.obj k
                (PeriodicComponentVertex T hT E) y)
              (MagnitudeConjecture.LinearPathCategory.obj k
                (PeriodicComponentVertex T hT E) x)).symm f')) =
      eqToHom (ambientComponentYonedaObjEq (k := k) T hT E y) ≫
        (CategoryTheory.linearYoneda k
          (PeriodicComponentMeshCategory T hT k E)).map
            ((quotientFunctor (k := k)
              (periodicComponentRightMeshData T hT E)).map
                ((MagnitudeConjecture.LinearPathCategory.homPathLinearEquiv
                  (MagnitudeConjecture.LinearPathCategory.obj k
                    (PeriodicComponentVertex T hT E) y)
                  (MagnitudeConjecture.LinearPathCategory.obj k
                    (PeriodicComponentVertex T hT E) x)).symm f')) ≫
          eqToHom
            (ambientComponentYonedaObjEq (k := k) T hT E x).symm
  induction f' using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ hf₁ hf₂ =>
      rw [(MagnitudeConjecture.LinearPathCategory.homPathLinearEquiv
          (MagnitudeConjecture.LinearPathCategory.obj k
            (PeriodicComponentVertex T hT E) y)
          (MagnitudeConjecture.LinearPathCategory.obj k
            (PeriodicComponentVertex T hT E) x)).symm.map_add,
        Functor.map_add
          (MagnitudeConjecture.LinearPathCategory.prefunctorFunctor
            (k := k) (periodicComponentInclusion T hT E)),
        Functor.map_add
          (ambientComponentYonedaRealization (k := k) T hT E).freeFunctor,
        Functor.map_add
          (quotientFunctor (k := k)
            (periodicComponentRightMeshData T hT E)),
        Functor.map_add
          (CategoryTheory.linearYoneda k
            (PeriodicComponentMeshCategory T hT k E)),
        Preadditive.add_comp, Preadditive.comp_add, hf₁, hf₂]
  | single p r =>
      rw [MagnitudeConjecture.LinearPathCategory.homPathLinearEquiv_symm_single]
      rw [Functor.map_smul
          (MagnitudeConjecture.LinearPathCategory.prefunctorFunctor
            (k := k) (periodicComponentInclusion T hT E)),
        Functor.map_smul
          (ambientComponentYonedaRealization (k := k) T hT E).freeFunctor,
        Functor.map_smul
          (quotientFunctor (k := k)
            (periodicComponentRightMeshData T hT E)),
        Functor.map_smul
          (CategoryTheory.linearYoneda k
            (PeriodicComponentMeshCategory T hT k E)),
        CategoryTheory.Linear.smul_comp,
        CategoryTheory.Linear.comp_smul]
      rw [MagnitudeConjecture.LinearPathCategory.prefunctorFunctor_map_pathHom,
        MagnitudeConjecture.LinearPathCategory.lift_map_pathHom]
      exact congrArg (fun q ↦ r • q)
        (ambientComponentYoneda_pathMap_inclusion (k := k) T hT E p)

/-- The transported Hom map from the ambient mesh category to the Hom space
between component representables. -/
def ambientComponentYonedaTransportLinearMap
    (E : PeriodicComponent T hT)
    (x y : PeriodicComponentVertex T hT E) :
    (obj (k := k) T y.1 ⟶ obj (k := k) T x.1) →ₗ[k]
      ((CategoryTheory.linearYoneda k
          (PeriodicComponentMeshCategory T hT k E)).obj
            (periodicComponentMeshObj (k := k) T hT y) ⟶
        (CategoryTheory.linearYoneda k
          (PeriodicComponentMeshCategory T hT k E)).obj
            (periodicComponentMeshObj (k := k) T hT x)) :=
  (CategoryTheory.Linear.rightComp k _
      (eqToHom (ambientComponentYonedaObjEq (k := k) T hT E x))).comp
    ((CategoryTheory.Linear.leftComp k _
      (eqToHom
        (ambientComponentYonedaObjEq (k := k) T hT E y).symm)).comp
      ((ambientComponentYonedaRealization
        (k := k) T hT E).functor.mapLinearMap k))

@[simp]
theorem ambientComponentYonedaTransportLinearMap_apply
    (E : PeriodicComponent T hT)
    (x y : PeriodicComponentVertex T hT E)
    (f : obj (k := k) T y.1 ⟶ obj (k := k) T x.1) :
    ambientComponentYonedaTransportLinearMap (k := k) T hT E x y f =
      eqToHom (ambientComponentYonedaObjEq (k := k) T hT E y).symm ≫
        (ambientComponentYonedaRealization (k := k) T hT E).functor.map f ≫
          eqToHom (ambientComponentYonedaObjEq (k := k) T hT E x) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Between component vertices, the descended ambient realization surjects
onto the Hom space between the corresponding component representables. -/
theorem ambientComponentYonedaFunctor_transport_surjective
    (E : PeriodicComponent T hT)
    (x y : PeriodicComponentVertex T hT E) :
    Function.Surjective
      (fun f : obj (k := k) T y.1 ⟶ obj (k := k) T x.1 ↦
        eqToHom (ambientComponentYonedaObjEq (k := k) T hT E y).symm ≫
          (ambientComponentYonedaRealization (k := k) T hT E).functor.map f ≫
            eqToHom (ambientComponentYonedaObjEq (k := k) T hT E x)) := by
  classical
  intro α
  let Y := CategoryTheory.linearYoneda k
    (PeriodicComponentMeshCategory T hT k E)
  obtain ⟨g, hg⟩ := Y.map_surjective α
  obtain ⟨f, hf⟩ :=
    (quotientFunctor (k := k)
      (periodicComponentRightMeshData T hT E)).map_surjective g
  refine ⟨(quotientFunctor (k := k) T).map
      ((MagnitudeConjecture.LinearPathCategory.prefunctorFunctor
        (k := k) (periodicComponentInclusion T hT E)).map f), ?_⟩
  dsimp only
  rw [(ambientComponentYonedaRealization
      (k := k) T hT E).functor_map_quotient_map]
  rw [ambientComponentYoneda_freeFunctor_map_inclusion
    (k := k) T hT E f]
  simp only [Category.assoc]
  have hyCancel :
      eqToHom (ambientComponentYonedaObjEq (k := k) T hT E y).symm ≫
          eqToHom (ambientComponentYonedaObjEq (k := k) T hT E y) =
        𝟙 _ := by simp
  have hxCancel :
      eqToHom (ambientComponentYonedaObjEq (k := k) T hT E x).symm ≫
          eqToHom (ambientComponentYonedaObjEq (k := k) T hT E x) =
        𝟙 _ := by simp
  rw [← Category.assoc
      (eqToHom (ambientComponentYonedaObjEq (k := k) T hT E y).symm)
      (eqToHom (ambientComponentYonedaObjEq (k := k) T hT E y)),
    hyCancel, Category.id_comp]
  change
    Y.map
          ((quotientFunctor (k := k)
            (periodicComponentRightMeshData T hT E)).map f) ≫
        (eqToHom
            (ambientComponentYonedaObjEq (k := k) T hT E x).symm ≫
          eqToHom (ambientComponentYonedaObjEq (k := k) T hT E x)) = α
  rw [hxCancel, Category.comp_id]
  rw [hf, hg]

/-- The bundled transported Hom map is surjective. -/
theorem ambientComponentYonedaTransportLinearMap_surjective
    (E : PeriodicComponent T hT)
    (x y : PeriodicComponentVertex T hT E) :
    Function.Surjective
      (ambientComponentYonedaTransportLinearMap (k := k) T hT E x y) := by
  intro α
  obtain ⟨f, hf⟩ :=
    ambientComponentYonedaFunctor_transport_surjective
      (k := k) T hT E x y α
  refine ⟨f, ?_⟩
  change
    eqToHom (ambientComponentYonedaObjEq (k := k) T hT E y).symm ≫
        (ambientComponentYonedaRealization (k := k) T hT E).functor.map f ≫
          eqToHom (ambientComponentYonedaObjEq (k := k) T hT E x) = α
  exact hf

/-- Finite-dimensionality of ambient mesh Hom spaces descends to every Hom
space of a periodic component mesh. -/
theorem periodicComponentMeshHomFinite
    (E : PeriodicComponent T hT)
    (hfinite : ∀ a b : Q,
      FiniteDimensional k
        (obj (k := k) T a ⟶ obj (k := k) T b))
    (x y : PeriodicComponentVertex T hT E) :
    FiniteDimensional k
      (periodicComponentMeshObj (k := k) T hT x ⟶
        periodicComponentMeshObj (k := k) T hT y) := by
  letI : FiniteDimensional k
      (obj (k := k) T x.1 ⟶ obj (k := k) T y.1) :=
    hfinite x.1 y.1
  let Y := CategoryTheory.linearYoneda k
    (PeriodicComponentMeshCategory T hT k E)
  letI : FiniteDimensional k
      (Y.obj (periodicComponentMeshObj (k := k) T hT x) ⟶
        Y.obj (periodicComponentMeshObj (k := k) T hT y)) :=
    FiniteDimensional.of_surjective
      (ambientComponentYonedaTransportLinearMap (k := k) T hT E y x)
      (ambientComponentYonedaTransportLinearMap_surjective
        (k := k) T hT E y x)
  exact FiniteDimensional.of_injective
    (Y.mapLinearMap k) Y.map_injective

end MagnitudeConjecture.MeshCategory.RightMeshData.IsTauInjective
