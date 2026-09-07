import MagnitudeConjecture.CategoryTheory.TranslationQuiverHomotopyLift
import MagnitudeConjecture.CategoryTheory.TranslationQuiverRiedtmannCover
import MagnitudeConjecture.CategoryTheory.TranslationQuiverRiedtmannDegree
import MagnitudeConjecture.CategoryTheory.TranslationQuiverSectionalPathContraction
import MagnitudeConjecture.CategoryTheory.TranslationQuiverDeckDegree
import Mathlib.Algebra.Group.Action.TransferInstance
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Comparing the based-walk and Riedtmann covers

The homotopy-invariant lift through a stable mesh cover is specialized to the
canonical Riedtmann repetition cover.  The resulting prefunctor starts at the
based-walk universal cover and lands in the repetition of the sectional-prefix
tree, while remaining a quiver covering over the original translation quiver.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RepetitionLine

private theorem prefunctor_map_cast_heq
    {U : Type*} {V : Type*} [Quiver U] [Quiver V]
    (F : Prefunctor U V) {x y x' y' : U}
    (hx : x = x') (hy : y = y') (a : x ⟶ y) :
    F.map (Quiver.Hom.cast hx hy a) ≍ F.map a := by
  cases hx
  cases hy
  rfl

/-- The canonical morphism in the free groupoid on the integer line from
zero to any integer. -/
def freeGroupoidHomFromZero (n : ℤ) :
    (Quiver.FreeGroupoid.of ℤ).obj 0 ⟶
      (Quiver.FreeGroupoid.of ℤ).obj n := by
  exact Int.inductionOn' n 0 (𝟙 _)
    (fun k _ ih ↦ ih ≫ Groupoid.inv
      ((Quiver.FreeGroupoid.of ℤ).map
        ((down (k + 1)).cast rfl (by omega))))
    (fun k _ ih ↦ ih ≫ (Quiver.FreeGroupoid.of ℤ).map (down k))

private theorem freeGroupoidHomFromZero_heq {n m : ℤ} (h : n = m) :
    freeGroupoidHomFromZero n ≍ freeGroupoidHomFromZero m := by
  subst m
  rfl

/-- The canonical root-to-level morphism followed by the downward generator
is the canonical morphism to the preceding level. -/
theorem freeGroupoidHomFromZero_comp_down (n : ℤ) :
    freeGroupoidHomFromZero n ≫
        (Quiver.FreeGroupoid.of ℤ).map (down n) =
      freeGroupoidHomFromZero (n - 1) := by
  by_cases hn : n ≤ 0
  · unfold freeGroupoidHomFromZero
    rw [Int.inductionOn'_sub_one hn]
  · obtain ⟨k, hk, rfl⟩ : ∃ k : ℤ, 0 ≤ k ∧ n = k + 1 :=
      ⟨n - 1, by omega, by omega⟩
    have hrec :
        freeGroupoidHomFromZero (k + 1) ≫
            (Quiver.FreeGroupoid.of ℤ).map
              ((down (k + 1)).cast rfl (by omega)) =
          freeGroupoidHomFromZero k := by
      unfold freeGroupoidHomFromZero
      rw [Int.inductionOn'_add_one hk]
      rw [Category.assoc, Groupoid.inv_eq_inv, IsIso.inv_hom_id,
        Category.comp_id]
    convert hrec using 1
    · exact congrArg
        (fun z ↦ (Quiver.FreeGroupoid.of ℤ).obj 0 ⟶
          (Quiver.FreeGroupoid.of ℤ).obj z) (by omega)
    · apply heq_comp rfl rfl (congrArg
        (fun z ↦ (Quiver.FreeGroupoid.of ℤ).obj z) (by omega)) HEq.rfl
      exact (prefunctor_map_cast_heq (Quiver.FreeGroupoid.of ℤ)
        rfl (by omega) (down (k + 1))).symm
    · exact freeGroupoidHomFromZero_heq (by omega)

/-- Every generating downward arrow is the difference of the canonical
root-to-level morphisms at its endpoints. -/
theorem freeGroupoid_map_down (n : ℤ) :
    (Quiver.FreeGroupoid.of ℤ).map (down n) =
      Groupoid.inv (freeGroupoidHomFromZero n) ≫
        freeGroupoidHomFromZero (n - 1) := by
  calc
    _ = 𝟙 _ ≫ (Quiver.FreeGroupoid.of ℤ).map (down n) :=
      (Category.id_comp _).symm
    _ = (Groupoid.inv (freeGroupoidHomFromZero n) ≫
          freeGroupoidHomFromZero n) ≫
        (Quiver.FreeGroupoid.of ℤ).map (down n) := by
      rw [Groupoid.inv_comp]
    _ = Groupoid.inv (freeGroupoidHomFromZero n) ≫
        (freeGroupoidHomFromZero n ≫
          (Quiver.FreeGroupoid.of ℤ).map (down n)) :=
      Category.assoc _ _ _
    _ = _ := by rw [freeGroupoidHomFromZero_comp_down]

/-- A morphism in the free groupoid on the integer line is determined by its
two endpoints. -/
private theorem path_quot_eq_canonical {n m : ℤ}
    (p : @Quiver.Path (Quiver.Symmetrify ℤ)
      (Quiver.symmetrifyQuiver ℤ) n m) :
    (Quot.mk _ p : (Quiver.FreeGroupoid.of ℤ).obj n ⟶
      (Quiver.FreeGroupoid.of ℤ).obj m) =
    Groupoid.inv (freeGroupoidHomFromZero n) ≫
      freeGroupoidHomFromZero m := by
  induction p with
  | nil =>
      change 𝟙 _ = Groupoid.inv (freeGroupoidHomFromZero n) ≫
        freeGroupoidHomFromZero n
      exact (Groupoid.inv_comp _).symm
  | cons p e ih =>
      rename_i b c
      change
        (CategoryTheory.Quotient.functor
          Quiver.FreeGroupoid.redStep).map p ≫
        (CategoryTheory.Quotient.functor
          Quiver.FreeGroupoid.redStep).map
          (@Quiver.Hom.toPath (Quiver.Symmetrify ℤ)
            (Quiver.symmetrifyQuiver ℤ) _ _ e) = _
      change
        (CategoryTheory.Quotient.functor
          Quiver.FreeGroupoid.redStep).map p = _ at ih
      rw [ih]
      rcases e with a | a
      · have h := a.down
        change c = b - 1 at h
        subst c
        have ha : a = down b := by
          rcases a with ⟨ha⟩
          rfl
        rw [ha]
        change
          (Groupoid.inv (freeGroupoidHomFromZero n) ≫
              freeGroupoidHomFromZero b) ≫
            (Quiver.FreeGroupoid.of ℤ).map (down b) =
          Groupoid.inv (freeGroupoidHomFromZero n) ≫
            freeGroupoidHomFromZero (b - 1)
        rw [Category.assoc,
          freeGroupoidHomFromZero_comp_down]
      · have h := a.down
        change b = c - 1 at h
        subst b
        have ha : a = down c := by
          rcases a with ⟨ha⟩
          rfl
        rw [ha]
        change
          (Groupoid.inv (freeGroupoidHomFromZero n) ≫
              freeGroupoidHomFromZero (c - 1)) ≫
            Groupoid.inv ((Quiver.FreeGroupoid.of ℤ).map (down c)) =
          Groupoid.inv (freeGroupoidHomFromZero n) ≫
            freeGroupoidHomFromZero c
        rw [freeGroupoid_map_down]
        simp only [Groupoid.inv_eq_inv]
        rw [IsIso.inv_comp, IsIso.inv_inv]
        simp only [Category.assoc, IsIso.hom_inv_id_assoc]

theorem freeGroupoid_hom_eq_canonical {n m : ℤ}
    (f : (Quiver.FreeGroupoid.of ℤ).obj n ⟶
      (Quiver.FreeGroupoid.of ℤ).obj m) :
    f = Groupoid.inv (freeGroupoidHomFromZero n) ≫
      freeGroupoidHomFromZero m := by
  exact Quot.inductionOn f (fun p ↦ path_quot_eq_canonical p)

/-- Every Hom set in the free groupoid on the oriented integer line is a
subsingleton. -/
theorem freeGroupoid_hom_subsingleton (n m : ℤ) :
    Subsingleton ((Quiver.FreeGroupoid.of ℤ).obj n ⟶
      (Quiver.FreeGroupoid.of ℤ).obj m) :=
  ⟨fun f g ↦ (freeGroupoid_hom_eq_canonical f).trans
    (freeGroupoid_hom_eq_canonical g).symm⟩

end MagnitudeConjecture.RepetitionLine

namespace MagnitudeConjecture.MeshCategory.RightMeshData

universe u v u₁ u₂ v₁ v₂

open UniversalCover

/-- The inverse prefunctor determined by compatible equivalences of vertices
and fixed arrow types. -/
private def inversePrefunctorOfEquiv
    {U : Type u₁} {V : Type u₂} [Quiver.{v₁} U] [Quiver.{v₂} V]
    (e : U ≃ V) (he : ∀ X Y : U, (X ⟶ Y) ≃ (e X ⟶ e Y)) :
    V ⥤q U where
  obj := e.symm
  map {X Y} a := (he _ _).symm
    (Quiver.homOfEq a (e.apply_symm_apply X).symm
      (e.apply_symm_apply Y).symm)

@[simp]
private theorem homOfEq_equiv_homOfEq
    {U : Type u₁} {V : Type u₂} [Quiver.{v₁} U] [Quiver.{v₂} V]
    (e : U ≃ V) (he : ∀ X Y : U, (X ⟶ Y) ≃ (e X ⟶ e Y))
    {X Y X' Y' : U} (f : X ⟶ Y) (hX : X = X') (hY : Y = Y')
    {X'' Y'' : V} (hX' : e X' = X'') (hY' : e Y' = Y'') :
    Quiver.homOfEq (he _ _ (Quiver.homOfEq f hX hY)) hX' hY' =
      Quiver.homOfEq (he _ _ f) (by rw [hX, hX']) (by rw [hY, hY']) := by
  subst hX hY hX' hY'
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The forward prefunctor associated to compatible vertex and arrow
equivalences is left inverse to the explicit inverse prefunctor. -/
private theorem prefunctorOfEquiv_comp_inverse
    {U : Type u₁} {V : Type u₂} [Quiver.{v₁} U] [Quiver.{v₂} V]
    (e : U ≃ V) (he : ∀ X Y : U, (X ⟶ Y) ≃ (e X ⟶ e Y)) :
    Prefunctor.mk e (he _ _) ⋙q inversePrefunctorOfEquiv e he = 𝟭q U := by
  have hobj : ∀ X : U,
      (Prefunctor.mk e (he _ _) ⋙q
        inversePrefunctorOfEquiv e he).obj X = (𝟭q U).obj X :=
    e.left_inv
  apply Prefunctor.ext' hobj
  intro X Y f
  dsimp [inversePrefunctorOfEquiv]
  apply (he _ _).injective
  apply Quiver.homOfEq_injective
    (X' := e X) (Y' := e Y) (by simp) (by simp)
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit inverse prefunctor is left inverse to the forward
prefunctor associated to compatible vertex and arrow equivalences. -/
private theorem inversePrefunctorOfEquiv_comp_prefunctor
    {U : Type u₁} {V : Type u₂} [Quiver.{v₁} U] [Quiver.{v₂} V]
    (e : U ≃ V) (he : ∀ X Y : U, (X ⟶ Y) ≃ (e X ⟶ e Y)) :
    inversePrefunctorOfEquiv e he ⋙q Prefunctor.mk e (he _ _) = 𝟭q V := by
  have hobj : ∀ X : V,
      (inversePrefunctorOfEquiv e he ⋙q
        Prefunctor.mk e (he _ _)).obj X = (𝟭q V).obj X :=
    e.right_inv
  apply Prefunctor.ext' hobj
  simp [inversePrefunctorOfEquiv]

/-- A quiver covering that is injective on vertices is bijective on each
fixed Hom type. -/
private theorem covering_map_bijective_of_obj_injective
    {U : Type*} {V : Type*} [Quiver U] [Quiver V]
    (F : Prefunctor U V) (hF : F.IsCovering)
    (hobj : Function.Injective F.obj) (X Y : U) :
    Function.Bijective
      (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
  constructor
  · exact hF.map_injective
  · intro a
    obtain ⟨⟨Z, b⟩, hb⟩ :=
      (hF.star_bijective X).2 (⟨F.obj Y, a⟩ : Quiver.Star (F.obj X))
    have hZ : Z = Y := hobj (congrArg Sigma.fst hb)
    subst Z
    exact ⟨b, eq_of_heq (Sigma.ext_iff.mp hb).2⟩

/-- The order of a finite group acting freely on a finite type divides the
cardinality of that type. -/
private theorem card_group_dvd_card_of_isCancelSMul
    {G : Type u₁} {X : Type u₂} [Group G] [MulAction G X]
    [IsCancelSMul G X] [Fintype G] [Fintype X] :
    Fintype.card G ∣ Fintype.card X := by
  let Ω := MulAction.orbitRel.Quotient G X
  letI : Fintype Ω := Fintype.ofFinite Ω
  letI orbitFintype (x : X) : Fintype (MulAction.orbit G x) :=
    Fintype.ofFinite _
  letI stabilizerFintype (x : X) :
      Fintype (MulAction.stabilizer G x) := Fintype.ofFinite _
  have horbit (x : X) :
      Fintype.card (MulAction.orbit G x) = Fintype.card G := by
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x
    simpa [IsCancelSMul.stabilizer_eq_bot] using h
  have hcard : Fintype.card X = Fintype.card Ω * Fintype.card G := by
    calc
      Fintype.card X =
          Fintype.card (Σ ω : Ω, MulAction.orbit G ω.out) :=
        Fintype.card_congr (MulAction.selfEquivSigmaOrbits G X)
      _ = ∑ ω : Ω, Fintype.card (MulAction.orbit G ω.out) :=
        Fintype.card_sigma
      _ = ∑ _ω : Ω, Fintype.card G := by
        simp_rw [horbit]
      _ = Fintype.card Ω * Fintype.card G := by simp
  exact ⟨Fintype.card Ω, by rw [mul_comm, ← hcard]⟩

variable {Q : Type u} [Quiver.{v} Q]
variable (T : RightMeshData Q)
variable (hstable : T.projective = ∅)
variable (hbijective : Function.Bijective (T.stableTau hstable))
variable (x₀ : Q)

namespace UniversalCover

/-- Transport the chosen base vertex of a based-walk universal cover along an
equality. -/
def castBasePrefunctor {x₀ x₁ : Q} (h : x₀ = x₁) :
    Vertex T x₀ ⥤q Vertex T x₁ := by
  subst x₁
  exact 𝟭q (Vertex T x₀)

/-- Base transport is a quiver covering. -/
theorem castBasePrefunctor_isCovering {x₀ x₁ : Q} (h : x₀ = x₁) :
    (castBasePrefunctor T h).IsCovering := by
  subst x₁
  constructor <;> intro W
  · exact Function.bijective_id
  · exact Function.bijective_id

/-- Base transport is bijective on universal-cover vertices. -/
theorem castBasePrefunctor_obj_bijective {x₀ x₁ : Q} (h : x₀ = x₁) :
    Function.Bijective (castBasePrefunctor T h).obj := by
  subst x₁
  exact Function.bijective_id

/-- Base transport does not alter the endpoint projection. -/
theorem castBasePrefunctor_comp_projection {x₀ x₁ : Q} (h : x₀ = x₁) :
    castBasePrefunctor T h ⋙q projection T x₁ = projection T x₀ := by
  subst x₁
  rfl

/-- Transporting the chosen universal-cover base does not change the signed
degree of a based-walk vertex. -/
theorem castBasePrefunctor_vertexDegree {x₀ x₁ : Q} (h : x₀ = x₁)
    (W : Vertex T x₀) :
    vertexDegree T x₁ ((castBasePrefunctor T h).obj W) =
      vertexDegree T x₀ W := by
  subst x₁
  rfl

end UniversalCover

namespace RiedtmannCover

/-- The level-zero root of the sectional-prefix repetition. -/
def baseVertex : (Tree T x₀).Vertex :=
  ⟨0, SectionalPath.root x₀⟩

/-- The canonical Riedtmann projection sends its chosen repetition root to
the chosen base vertex downstairs. -/
theorem projection_baseVertex :
    (projection T hstable hbijective x₀).obj (baseVertex T x₀) = x₀ := by
  change shiftedVertex T hstable hbijective 0 x₀ = x₀
  exact shiftedVertex_zero T hstable hbijective x₀

private theorem sourceStableTau_bijective :
    Function.Bijective
      ((Tree T x₀).rightMeshData.stableTau
        (Tree T x₀).rightMeshData_projective) := by
  change Function.Bijective (Tree T x₀).tauVertex
  exact (Tree T x₀).tauVertex_bijective

/-- The canonical morphism in the repetition mesh-homotopy groupoid from the
chosen level-zero root to any repetition vertex. -/
def baseToVertexMorphism (X : (Tree T x₀).Vertex) :
    (show HomotopyGroupoid (Tree T x₀).rightMeshData from
      baseVertex T x₀) ⟶
    (show HomotopyGroupoid (Tree T x₀).rightMeshData from X) :=
  ((Tree T x₀).rootLineFunctor (SectionalPath.root x₀)).map
      (MagnitudeConjecture.RepetitionLine.freeGroupoidHomFromZero X.level) ≫
    (SectionalPath.rootRetractionIso (T := T) x₀).hom.app X

/-- Choose an augmented-walk representative of the canonical root-to-vertex
morphism in the repetition. -/
def baseToVertexWalk (X : (Tree T x₀).Vertex) :
    Walk (Tree T x₀).rightMeshData (baseVertex T x₀) X :=
  Quotient.out (baseToVertexMorphism T x₀ X)

/-- The sectional-prefix repetition is augmented-walk connected at its
level-zero root. -/
theorem source_isWalkConnectedAt :
    IsWalkConnectedAt (Tree T x₀).rightMeshData (baseVertex T x₀) :=
  fun X ↦ ⟨baseToVertexWalk T x₀ X⟩

/-- The mesh-homotopy groupoid of the sectional-prefix repetition has at most
one morphism between any two vertices. -/
theorem sourceHomotopyGroupoid_hom_subsingleton
    (X Y : HomotopyGroupoid (Tree T x₀).rightMeshData) :
    Subsingleton (X ⟶ Y) := by
  constructor
  intro f g
  let E := SectionalPath.repetitionHomotopyEquivalence (T := T) x₀
  apply E.functor.map_injective
  exact (MagnitudeConjecture.RepetitionLine.freeGroupoid_hom_subsingleton
    (show (Tree T x₀).Vertex from X).level
    (show (Tree T x₀).Vertex from Y).level).elim _ _

/-- Any two augmented walks in the repetition with the same endpoints are
mesh-homotopic. -/
theorem source_walk_homotopic {X Y : (Tree T x₀).Vertex}
    (p q : Walk (Tree T x₀).rightMeshData X Y) :
    Homotopic (Tree T x₀).rightMeshData X p q := by
  change (homotopySetoid (Tree T x₀).rightMeshData X Y).r p q
  apply Quotient.exact
  exact (sourceHomotopyGroupoid_hom_subsingleton T x₀ X Y).elim _ _

/-- The based-walk universal cover at the literal image of the repetition
root maps canonically into the Riedtmann repetition. -/
def basedUniversalLift :
    Vertex T
        ((projection T hstable hbijective x₀).obj (baseVertex T x₀)) ⥤q
      (Tree T x₀).Vertex :=
  (cover T hstable hbijective x₀).liftVertexPrefunctor
    (Tree T x₀).rightMeshData_projective hstable
    (sourceStableTau_bijective T x₀) hbijective (baseVertex T x₀)

@[simp]
theorem basedUniversalLift_obj
    (W : Vertex T
      ((projection T hstable hbijective x₀).obj (baseVertex T x₀))) :
    (basedUniversalLift T hstable hbijective x₀).obj W =
      (cover T hstable hbijective x₀).liftVertex
        (Tree T x₀).rightMeshData_projective hstable
        (sourceStableTau_bijective T x₀) hbijective
        (baseVertex T x₀) W :=
  rfl

/-- The Riedtmann lift followed by the Riedtmann projection is the canonical
based-walk universal-cover projection. -/
theorem basedUniversalLift_comp_projection :
    basedUniversalLift T hstable hbijective x₀ ⋙q
        projection T hstable hbijective x₀ =
      UniversalCover.projection T
        ((projection T hstable hbijective x₀).obj (baseVertex T x₀)) :=
  (cover T hstable hbijective x₀).liftVertexPrefunctor_comp_projection
    (Tree T x₀).rightMeshData_projective hstable
    (sourceStableTau_bijective T x₀) hbijective (baseVertex T x₀)

/-- The comparison from the based-walk cover to the Riedtmann repetition is
itself a quiver covering. -/
theorem basedUniversalLift_isCovering :
    (basedUniversalLift T hstable hbijective x₀).IsCovering :=
  (cover T hstable hbijective x₀).liftVertexPrefunctor_isCovering
    (Tree T x₀).rightMeshData_projective hstable
    (sourceStableTau_bijective T x₀) hbijective (baseVertex T x₀)

/-- Every repetition vertex is represented by a lifted target based-walk
class. -/
theorem basedUniversalLift_obj_surjective :
    Function.Surjective (basedUniversalLift T hstable hbijective x₀).obj :=
  (cover T hstable hbijective x₀).liftVertexPrefunctor_obj_surjective
    (Tree T x₀).rightMeshData_projective hstable
    (sourceStableTau_bijective T x₀) hbijective (baseVertex T x₀)
    (source_isWalkConnectedAt T x₀)

/-- The based-walk comparison distinguishes repetition vertices. -/
theorem basedUniversalLift_obj_injective :
    Function.Injective (basedUniversalLift T hstable hbijective x₀).obj :=
  (cover T hstable hbijective x₀).liftVertex_injective
    (Tree T x₀).rightMeshData_projective hstable
    (sourceStableTau_bijective T x₀) hbijective (baseVertex T x₀)
    (fun p q ↦ source_walk_homotopic T x₀ p q)

/-- The based-walk comparison is bijective on vertices. -/
theorem basedUniversalLift_obj_bijective :
    Function.Bijective (basedUniversalLift T hstable hbijective x₀).obj :=
  ⟨basedUniversalLift_obj_injective T hstable hbijective x₀,
    basedUniversalLift_obj_surjective T hstable hbijective x₀⟩

/-- The repetition degree of a based Riedtmann lift is the signed walk degree
of the original universal-cover vertex. -/
theorem basedUniversalLift_obj_repetitionDegree
    (W : Vertex T
      ((projection T hstable hbijective x₀).obj (baseVertex T x₀))) :
    SectionalPath.repetitionDegree (T := T) x₀
        ((basedUniversalLift T hstable hbijective x₀).obj W) =
      vertexDegree T
        ((projection T hstable hbijective x₀).obj (baseVertex T x₀)) W := by
  rcases W with ⟨y, W⟩
  induction W using Quotient.inductionOn with
  | _ p =>
      let L := (cover T hstable hbijective x₀).liftWalk
        (Tree T x₀).rightMeshData_projective hstable
        (sourceStableTau_bijective T x₀) hbijective
        (baseVertex T x₀) p
      have hlift := (cover T hstable hbijective x₀).liftWalk_walkDegree
        (Tree T x₀).rightMeshData_projective hstable
        (sourceStableTau_bijective T x₀) hbijective
        (baseVertex T x₀) p
      have hrep := SectionalPath.repetition_walkDegree_eq (T := T) x₀ L.2
      change SectionalPath.repetitionDegree (T := T) x₀ L.1 =
        walkDegree T p
      change walkDegree (Tree T x₀).rightMeshData L.2 =
        walkDegree T p at hlift
      change walkDegree (Tree T x₀).rightMeshData L.2 =
          SectionalPath.repetitionDegree (T := T) x₀ L.1 -
            SectionalPath.repetitionDegree (T := T) x₀
              (baseVertex T x₀) at hrep
      have hbase : SectionalPath.repetitionDegree (T := T) x₀
          (baseVertex T x₀) = 0 := rfl
      rw [hbase, sub_zero] at hrep
      exact hrep.symm.trans hlift

/-- The Riedtmann comparison with the based-walk cover normalized to the
original chosen base vertex `x₀`. -/
def universalLift :
    Vertex T x₀ ⥤q (Tree T x₀).Vertex :=
  UniversalCover.castBasePrefunctor T
      (projection_baseVertex T hstable hbijective x₀).symm ⋙q
    basedUniversalLift T hstable hbijective x₀

/-- The normalized Riedtmann comparison remains over the original
translation quiver. -/
theorem universalLift_comp_projection :
    universalLift T hstable hbijective x₀ ⋙q
        projection T hstable hbijective x₀ =
      UniversalCover.projection T x₀ := by
  unfold universalLift
  rw [Prefunctor.comp_assoc,
    basedUniversalLift_comp_projection T hstable hbijective x₀]
  exact UniversalCover.castBasePrefunctor_comp_projection T
    (projection_baseVertex T hstable hbijective x₀).symm

/-- The normalized comparison from the based-walk universal cover to the
Riedtmann repetition is a quiver covering. -/
theorem universalLift_isCovering :
    (universalLift T hstable hbijective x₀).IsCovering :=
  Prefunctor.IsCovering.comp
    (φ := UniversalCover.castBasePrefunctor T
      (projection_baseVertex T hstable hbijective x₀).symm)
    (ψ := basedUniversalLift T hstable hbijective x₀)
    (UniversalCover.castBasePrefunctor_isCovering T
      (projection_baseVertex T hstable hbijective x₀).symm)
    (basedUniversalLift_isCovering T hstable hbijective x₀)

/-- The normalized comparison is surjective on repetition vertices. -/
theorem universalLift_obj_surjective :
    Function.Surjective (universalLift T hstable hbijective x₀).obj := by
  change Function.Surjective
    ((basedUniversalLift T hstable hbijective x₀).obj ∘
      (UniversalCover.castBasePrefunctor T
        (projection_baseVertex T hstable hbijective x₀).symm).obj)
  exact (basedUniversalLift_obj_surjective T hstable hbijective x₀).comp
    (UniversalCover.castBasePrefunctor_obj_bijective T
      (projection_baseVertex T hstable hbijective x₀).symm).2

/-- The normalized comparison is injective on based-walk vertices. -/
theorem universalLift_obj_injective :
    Function.Injective (universalLift T hstable hbijective x₀).obj := by
  change Function.Injective
    ((basedUniversalLift T hstable hbijective x₀).obj ∘
      (UniversalCover.castBasePrefunctor T
        (projection_baseVertex T hstable hbijective x₀).symm).obj)
  exact (basedUniversalLift_obj_injective T hstable hbijective x₀).comp
    (UniversalCover.castBasePrefunctor_obj_bijective T
      (projection_baseVertex T hstable hbijective x₀).symm).1

/-- The normalized Riedtmann comparison is bijective on vertices. -/
theorem universalLift_obj_bijective :
    Function.Bijective (universalLift T hstable hbijective x₀).obj :=
  ⟨universalLift_obj_injective T hstable hbijective x₀,
    universalLift_obj_surjective T hstable hbijective x₀⟩

/-- The normalized Riedtmann comparison identifies the canonical degree on
the based-walk universal cover with the explicit repetition degree. -/
theorem universalLift_obj_repetitionDegree (W : Vertex T x₀) :
    SectionalPath.repetitionDegree (T := T) x₀
        ((universalLift T hstable hbijective x₀).obj W) =
      vertexDegree T x₀ W := by
  change SectionalPath.repetitionDegree (T := T) x₀
      ((basedUniversalLift T hstable hbijective x₀).obj
        ((UniversalCover.castBasePrefunctor T
          (projection_baseVertex T hstable hbijective x₀).symm).obj W)) = _
  rw [basedUniversalLift_obj_repetitionDegree T hstable hbijective x₀]
  exact UniversalCover.castBasePrefunctor_vertexDegree T
    (projection_baseVertex T hstable hbijective x₀).symm W

/-- The vertex equivalence underlying the normalized Riedtmann comparison. -/
def universalVertexEquiv :
    Vertex T x₀ ≃ (Tree T x₀).Vertex :=
  Equiv.ofBijective (universalLift T hstable hbijective x₀).obj
    (universalLift_obj_bijective T hstable hbijective x₀)

@[simp]
theorem universalVertexEquiv_apply (W : Vertex T x₀) :
    universalVertexEquiv T hstable hbijective x₀ W =
      (universalLift T hstable hbijective x₀).obj W :=
  rfl

/-- The Riedtmann vertex equivalence lies over the original translation
quiver. -/
theorem universalVertexEquiv_projection (W : Vertex T x₀) :
    (projection T hstable hbijective x₀).obj
        (universalVertexEquiv T hstable hbijective x₀ W) = W.1 := by
  exact Prefunctor.congr_obj
    (universalLift_comp_projection T hstable hbijective x₀) W

/-- Transport one canonical fundamental-group deck transformation from the
based-walk universal cover to the Riedtmann repetition. -/
def repetitionDeckActVertex
    (g : FundamentalGroup T x₀) (X : (Tree T x₀).Vertex) :
    (Tree T x₀).Vertex :=
  universalVertexEquiv T hstable hbijective x₀
    (g • (universalVertexEquiv T hstable hbijective x₀).symm X)

/-- The identity fundamental-group element acts identically on Riedtmann
vertices. -/
@[simp]
theorem repetitionDeckActVertex_one (X : (Tree T x₀).Vertex) :
    repetitionDeckActVertex T hstable hbijective x₀ 1 X = X := by
  simp [repetitionDeckActVertex]

/-- Multiplication of fundamental-group elements agrees with composition of
their transported actions. -/
theorem repetitionDeckActVertex_mul
    (g h : FundamentalGroup T x₀) (X : (Tree T x₀).Vertex) :
    repetitionDeckActVertex T hstable hbijective x₀ (g * h) X =
      repetitionDeckActVertex T hstable hbijective x₀ g
        (repetitionDeckActVertex T hstable hbijective x₀ h X) := by
  unfold repetitionDeckActVertex
  rw [mul_smul,
    (universalVertexEquiv T hstable hbijective x₀).symm_apply_apply]

/-- The Riedtmann vertex equivalence is equivariant for the original and
transported deck actions. -/
@[simp]
theorem universalVertexEquiv_smul
    (g : FundamentalGroup T x₀) (W : Vertex T x₀) :
    universalVertexEquiv T hstable hbijective x₀ (g • W) =
      repetitionDeckActVertex T hstable hbijective x₀ g
        (universalVertexEquiv T hstable hbijective x₀ W) := by
  rw [repetitionDeckActVertex,
    (universalVertexEquiv T hstable hbijective x₀).symm_apply_apply]

/-- The transported deck action fixes the Riedtmann projection. -/
theorem repetitionFundamentalGroup_projection_smul
    (g : FundamentalGroup T x₀) (X : (Tree T x₀).Vertex) :
    (projection T hstable hbijective x₀).obj
        (repetitionDeckActVertex T hstable hbijective x₀ g X) =
      (projection T hstable hbijective x₀).obj X := by
  calc
    _ = (g • (universalVertexEquiv T hstable hbijective x₀).symm X).1 :=
      universalVertexEquiv_projection T hstable hbijective x₀ _
    _ = ((universalVertexEquiv T hstable hbijective x₀).symm X).1 :=
      deckActVertex_vertex T x₀ g _
    _ = (projection T hstable hbijective x₀).obj
        (universalVertexEquiv T hstable hbijective x₀
          ((universalVertexEquiv T hstable hbijective x₀).symm X)) :=
      (universalVertexEquiv_projection T hstable hbijective x₀ _).symm
    _ = _ := congrArg (projection T hstable hbijective x₀).obj
      ((universalVertexEquiv T hstable hbijective x₀).apply_symm_apply X)

/-- The transported fundamental-group action on the Riedtmann repetition is
free at every vertex. -/
theorem repetitionFundamentalGroup_smul_injective
    (X : (Tree T x₀).Vertex) :
    Function.Injective (fun g : FundamentalGroup T x₀ ↦
      repetitionDeckActVertex T hstable hbijective x₀ g X) := by
  intro g h hgh
  apply deck_smul_injective T x₀
    ((universalVertexEquiv T hstable hbijective x₀).symm X)
  have h := congrArg
    (universalVertexEquiv T hstable hbijective x₀).symm hgh
  simpa only [repetitionDeckActVertex,
    (universalVertexEquiv T hstable hbijective x₀).symm_apply_apply] using h

/-- Two Riedtmann vertices have the same image downstairs exactly when one is
the transported deck translate of the other. -/
theorem repetition_projection_eq_iff_exists_deckAct
    (X Y : (Tree T x₀).Vertex) :
    (projection T hstable hbijective x₀).obj X =
        (projection T hstable hbijective x₀).obj Y ↔
      ∃ g : FundamentalGroup T x₀,
        repetitionDeckActVertex T hstable hbijective x₀ g X = Y := by
  let E := universalVertexEquiv T hstable hbijective x₀
  have hX : (projection T hstable hbijective x₀).obj X =
      (E.symm X).1 := by
    calc
      _ = (projection T hstable hbijective x₀).obj (E (E.symm X)) :=
        congrArg (projection T hstable hbijective x₀).obj
          (E.apply_symm_apply X).symm
      _ = _ := universalVertexEquiv_projection T hstable hbijective x₀ _
  have hY : (projection T hstable hbijective x₀).obj Y =
      (E.symm Y).1 := by
    calc
      _ = (projection T hstable hbijective x₀).obj (E (E.symm Y)) :=
        congrArg (projection T hstable hbijective x₀).obj
          (E.apply_symm_apply Y).symm
      _ = _ := universalVertexEquiv_projection T hstable hbijective x₀ _
  constructor
  · intro hXY
    obtain ⟨g, hg⟩ := exists_smul_eq_of_vertex_eq T x₀
      (E.symm X) (E.symm Y) (hX.symm.trans (hXY.trans hY))
    refine ⟨g, ?_⟩
    exact (congrArg E hg).trans (E.apply_symm_apply Y)
  · rintro ⟨g, rfl⟩
    exact (repetitionFundamentalGroup_projection_smul
      T hstable hbijective x₀ g X).symm

/-- The transported deck element carrying one vertex to another vertex in
the same projection fibre is unique. -/
theorem existsUnique_deckAct_eq_of_projection_eq
    (X Y : (Tree T x₀).Vertex)
    (hXY : (projection T hstable hbijective x₀).obj X =
      (projection T hstable hbijective x₀).obj Y) :
    ∃! g : FundamentalGroup T x₀,
      repetitionDeckActVertex T hstable hbijective x₀ g X = Y := by
  obtain ⟨g, hg⟩ :=
    (repetition_projection_eq_iff_exists_deckAct
      T hstable hbijective x₀ X Y).1 hXY
  exact ⟨g, hg, fun h hh ↦
    repetitionFundamentalGroup_smul_injective
      T hstable hbijective x₀ X (hh.trans hg.symm)⟩

/-- The transported deck action changes repetition degree by the original
fundamental-group degree. -/
theorem repetitionDegree_deckActVertex
    (g : FundamentalGroup T x₀) (X : (Tree T x₀).Vertex) :
    SectionalPath.repetitionDegree (T := T) x₀
        (repetitionDeckActVertex T hstable hbijective x₀ g X) =
      (fundamentalDegree T x₀ g).toAdd +
        SectionalPath.repetitionDegree (T := T) x₀ X := by
  let E := universalVertexEquiv T hstable hbijective x₀
  let W := E.symm X
  have hW : SectionalPath.repetitionDegree (T := T) x₀ (E W) =
      vertexDegree T x₀ W := by
    simpa [E] using
      universalLift_obj_repetitionDegree T hstable hbijective x₀ W
  calc
    _ = vertexDegree T x₀ (g • W) :=
      universalLift_obj_repetitionDegree T hstable hbijective x₀ _
    _ = (fundamentalDegree T x₀ g).toAdd +
        vertexDegree T x₀ W := vertexDegree_smul T x₀ g W
    _ = (fundamentalDegree T x₀ g).toAdd +
        SectionalPath.repetitionDegree (T := T) x₀ (E W) :=
      congrArg (fun n : ℤ ↦ (fundamentalDegree T x₀ g).toAdd + n)
        hW.symm
    _ = _ := congrArg
      (fun Z : (Tree T x₀).Vertex ↦
        (fundamentalDegree T x₀ g).toAdd +
          SectionalPath.repetitionDegree (T := T) x₀ Z)
      (show E W = X from E.apply_symm_apply X)

/-- The arrow equivalence over a pair of based-walk vertices. -/
def universalArrowEquiv (W Z : Vertex T x₀) :
    (W ⟶ Z) ≃
      (universalVertexEquiv T hstable hbijective x₀ W ⟶
        universalVertexEquiv T hstable hbijective x₀ Z) :=
  Equiv.ofBijective
    ((universalLift T hstable hbijective x₀).map :
      (W ⟶ Z) →
        ((universalLift T hstable hbijective x₀).obj W ⟶
          (universalLift T hstable hbijective x₀).obj Z))
    (covering_map_bijective_of_obj_injective
      (universalLift T hstable hbijective x₀)
      (universalLift_isCovering T hstable hbijective x₀)
      (universalLift_obj_injective T hstable hbijective x₀) W Z)

/-- The normalized comparison is bijective on every fixed arrow type.  With
`universalVertexEquiv`, this is the full quiver-isomorphism datum; it is kept
unbundled because Mathlib's bundled `Quiv` isomorphisms require the two arrow
types to inhabit the same universe. -/
theorem universalLift_map_bijective (W Z : Vertex T x₀) :
    Function.Bijective
      ((universalLift T hstable hbijective x₀).map :
        (W ⟶ Z) →
          ((universalLift T hstable hbijective x₀).obj W ⟶
            (universalLift T hstable hbijective x₀).obj Z)) :=
  covering_map_bijective_of_obj_injective
    (universalLift T hstable hbijective x₀)
    (universalLift_isCovering T hstable hbijective x₀)
    (universalLift_obj_injective T hstable hbijective x₀) W Z

/-- The inverse quiver map to the normalized Riedtmann comparison.  Endpoint
casts are needed because the inverse vertex equivalence is only propositionally
inverse to the comparison on objects. -/
def universalLiftInverse :
    (Tree T x₀).Vertex ⥤q Vertex T x₀ :=
  inversePrefunctorOfEquiv
      (universalVertexEquiv T hstable hbijective x₀)
      (universalArrowEquiv T hstable hbijective x₀)

@[simp]
theorem universalLiftInverse_obj (X : (Tree T x₀).Vertex) :
    (universalLiftInverse T hstable hbijective x₀).obj X =
      (universalVertexEquiv T hstable hbijective x₀).symm X :=
  rfl

/-- The normalized comparison followed by its explicit inverse is the
identity prefunctor on the based-walk universal cover. -/
theorem universalLift_comp_inverse :
    universalLift T hstable hbijective x₀ ⋙q
        universalLiftInverse T hstable hbijective x₀ =
      𝟭q (Vertex T x₀) := by
  exact prefunctorOfEquiv_comp_inverse
    (universalVertexEquiv T hstable hbijective x₀)
    (universalArrowEquiv T hstable hbijective x₀)

/-- The explicit inverse followed by the normalized comparison is the
identity prefunctor on the Riedtmann repetition. -/
theorem universalLiftInverse_comp_lift :
    universalLiftInverse T hstable hbijective x₀ ⋙q
        universalLift T hstable hbijective x₀ =
      𝟭q ((Tree T x₀).Vertex) := by
  exact inversePrefunctorOfEquiv_comp_prefunctor
    (universalVertexEquiv T hstable hbijective x₀)
    (universalArrowEquiv T hstable hbijective x₀)

/-- The inverse Riedtmann comparison is again a quiver covering. -/
theorem universalLiftInverse_isCovering :
    (universalLiftInverse T hstable hbijective x₀).IsCovering := by
  refine Prefunctor.IsCovering.of_comp_right
    (universalLiftInverse T hstable hbijective x₀)
    (universalLift T hstable hbijective x₀)
    (universalLift_isCovering T hstable hbijective x₀) ?_
  rw [universalLiftInverse_comp_lift]
  constructor <;> intro X
  · exact Function.bijective_id
  · exact Function.bijective_id

/-- One fundamental-group deck transformation transported to the Riedtmann
repetition as a quiver prefunctor. -/
def repetitionDeckPrefunctor (g : FundamentalGroup T x₀) :
    (Tree T x₀).Vertex ⥤q (Tree T x₀).Vertex :=
  universalLiftInverse T hstable hbijective x₀ ⋙q
    UniversalCover.deckPrefunctor T x₀ g ⋙q
      universalLift T hstable hbijective x₀

@[simp]
theorem repetitionDeckPrefunctor_obj
    (g : FundamentalGroup T x₀) (X : (Tree T x₀).Vertex) :
    (repetitionDeckPrefunctor T hstable hbijective x₀ g).obj X =
      repetitionDeckActVertex T hstable hbijective x₀ g X :=
  rfl

/-- Every transported deck transformation is a covering of the repetition
quiver. -/
theorem repetitionDeckPrefunctor_isCovering
    (g : FundamentalGroup T x₀) :
    (repetitionDeckPrefunctor T hstable hbijective x₀ g).IsCovering :=
  Prefunctor.IsCovering.comp
    (φ := universalLiftInverse T hstable hbijective x₀ ⋙q
      UniversalCover.deckPrefunctor T x₀ g)
    (ψ := universalLift T hstable hbijective x₀)
    (Prefunctor.IsCovering.comp
      (φ := universalLiftInverse T hstable hbijective x₀)
      (ψ := UniversalCover.deckPrefunctor T x₀ g)
      (universalLiftInverse_isCovering T hstable hbijective x₀)
      (UniversalCover.deckPrefunctor_isCovering T x₀ g))
    (universalLift_isCovering T hstable hbijective x₀)

/-- A transported deck prefunctor fixes the canonical Riedtmann projection
on vertices and arrows. -/
theorem repetitionDeckPrefunctor_comp_projection
    (g : FundamentalGroup T x₀) :
    repetitionDeckPrefunctor T hstable hbijective x₀ g ⋙q
        projection T hstable hbijective x₀ =
      projection T hstable hbijective x₀ := by
  unfold repetitionDeckPrefunctor
  rw [Prefunctor.comp_assoc, Prefunctor.comp_assoc,
    universalLift_comp_projection]
  rw [UniversalCover.deckPrefunctor_comp_projection]
  rw [← universalLift_comp_projection T hstable hbijective x₀]
  rw [← Prefunctor.comp_assoc, universalLiftInverse_comp_lift]
  rfl

/-- A transported deck transformation is bijective on repetition vertices. -/
def repetitionDeckVertexEquiv (g : FundamentalGroup T x₀) :
    (Tree T x₀).Vertex ≃ (Tree T x₀).Vertex where
  toFun := repetitionDeckActVertex T hstable hbijective x₀ g
  invFun := repetitionDeckActVertex T hstable hbijective x₀ g⁻¹
  left_inv X := by
    calc
      repetitionDeckActVertex T hstable hbijective x₀ g⁻¹
          (repetitionDeckActVertex T hstable hbijective x₀ g X) =
        repetitionDeckActVertex T hstable hbijective x₀ (g⁻¹ * g) X :=
          (repetitionDeckActVertex_mul T hstable hbijective x₀ g⁻¹ g X).symm
      _ = X := by simp
  right_inv X := by
    calc
      repetitionDeckActVertex T hstable hbijective x₀ g
          (repetitionDeckActVertex T hstable hbijective x₀ g⁻¹ X) =
        repetitionDeckActVertex T hstable hbijective x₀ (g * g⁻¹) X :=
          (repetitionDeckActVertex_mul T hstable hbijective x₀ g g⁻¹ X).symm
      _ = X := by simp

@[simp]
theorem repetitionDeckVertexEquiv_apply
    (g : FundamentalGroup T x₀) (X : (Tree T x₀).Vertex) :
    repetitionDeckVertexEquiv T hstable hbijective x₀ g X =
      repetitionDeckActVertex T hstable hbijective x₀ g X :=
  rfl

/-- A transported deck transformation is bijective on every fixed arrow
type, completing its unbundled quiver-automorphism data. -/
def repetitionDeckArrowEquiv (g : FundamentalGroup T x₀)
    (X Y : (Tree T x₀).Vertex) :
    (X ⟶ Y) ≃
      (repetitionDeckVertexEquiv T hstable hbijective x₀ g X ⟶
        repetitionDeckVertexEquiv T hstable hbijective x₀ g Y) :=
  Equiv.ofBijective
    ((repetitionDeckPrefunctor T hstable hbijective x₀ g).map :
      (X ⟶ Y) →
        ((repetitionDeckPrefunctor T hstable hbijective x₀ g).obj X ⟶
          (repetitionDeckPrefunctor T hstable hbijective x₀ g).obj Y))
    (covering_map_bijective_of_obj_injective
      (repetitionDeckPrefunctor T hstable hbijective x₀ g)
      (repetitionDeckPrefunctor_isCovering T hstable hbijective x₀ g)
      (repetitionDeckVertexEquiv T hstable hbijective x₀ g).injective X Y)

/-- The explicit inverse quiver map supplied by the transported deck
automorphism data. -/
def repetitionDeckPrefunctorInverse (g : FundamentalGroup T x₀) :
    (Tree T x₀).Vertex ⥤q (Tree T x₀).Vertex :=
  inversePrefunctorOfEquiv
    (repetitionDeckVertexEquiv T hstable hbijective x₀ g)
    (repetitionDeckArrowEquiv T hstable hbijective x₀ g)

/-- Each transported deck prefunctor has the displayed right inverse. -/
theorem repetitionDeckPrefunctor_comp_inverse
    (g : FundamentalGroup T x₀) :
    repetitionDeckPrefunctor T hstable hbijective x₀ g ⋙q
        repetitionDeckPrefunctorInverse T hstable hbijective x₀ g =
      𝟭q ((Tree T x₀).Vertex) :=
  prefunctorOfEquiv_comp_inverse
    (repetitionDeckVertexEquiv T hstable hbijective x₀ g)
    (repetitionDeckArrowEquiv T hstable hbijective x₀ g)

/-- Each transported deck prefunctor has the displayed left inverse. -/
theorem repetitionDeckPrefunctor_inverse_comp
    (g : FundamentalGroup T x₀) :
    repetitionDeckPrefunctorInverse T hstable hbijective x₀ g ⋙q
        repetitionDeckPrefunctor T hstable hbijective x₀ g =
      𝟭q ((Tree T x₀).Vertex) :=
  inversePrefunctorOfEquiv_comp_prefunctor
    (repetitionDeckVertexEquiv T hstable hbijective x₀ g)
    (repetitionDeckArrowEquiv T hstable hbijective x₀ g)

include hstable hbijective in
/-- If the Riedtmann tree class is finite, the subgroup of deck
transformations with zero integer degree is finite.  Its orbit of any one
repetition vertex injects into that vertex's finite degree slice. -/
theorem fundamentalDegree_ker_finite
    [Finite (T.SectionalPath x₀)] :
    Finite (MonoidHom.ker (fundamentalDegree T x₀)) := by
  let X := baseVertex T x₀
  let d := SectionalPath.repetitionDegree (T := T) x₀ X
  let f : MonoidHom.ker (fundamentalDegree T x₀) →
      {Y : (Tree T x₀).Vertex //
        SectionalPath.repetitionDegree (T := T) x₀ Y = d} :=
    fun g ↦ ⟨repetitionDeckActVertex T hstable hbijective x₀ g.1 X, by
      rw [repetitionDegree_deckActVertex]
      have hg : fundamentalDegree T x₀ g.1 = 1 := g.2
      rw [hg]
      rfl⟩
  letI : Finite {Y : (Tree T x₀).Vertex //
      SectionalPath.repetitionDegree (T := T) x₀ Y = d} :=
    SectionalPath.repetitionDegree_fiber_finite (T := T) x₀ d
  apply Finite.of_injective f
  intro g h hgh
  apply Subtype.ext
  apply repetitionFundamentalGroup_smul_injective
    T hstable hbijective x₀ X
  exact congrArg Subtype.val hgh

/-- The zero-degree deck subgroup acts on the two consecutive repetition
degree slices forming the canonical finite tree window. -/
@[reducible]
def fundamentalDegreeKernelDegreeWindowMulAction :
    MulAction (MonoidHom.ker (fundamentalDegree T x₀))
      (SectionalPath.DegreeWindow (T := T) x₀) where
  smul g X :=
    ⟨repetitionDeckActVertex T hstable hbijective x₀ g.1 X.1, by
      have hdegree := repetitionDegree_deckActVertex
        T hstable hbijective x₀ g.1 X.1
      rw [g.2] at hdegree
      have hdegree' : SectionalPath.repetitionDegree (T := T) x₀
          (repetitionDeckActVertex T hstable hbijective x₀ g.1 X.1) =
          SectionalPath.repetitionDegree (T := T) x₀ X.1 := by
        simpa using hdegree
      rw [hdegree']
      exact X.2⟩
  one_smul X := by
    apply Subtype.ext
    exact repetitionDeckActVertex_one T hstable hbijective x₀ X.1
  mul_smul g h X := by
    apply Subtype.ext
    exact repetitionDeckActVertex_mul
      T hstable hbijective x₀ g.1 h.1 X.1

/-- The zero-degree subgroup acts freely on the canonical two-degree
window. -/
theorem fundamentalDegreeKernelDegreeWindowIsCancelSMul :
    letI := fundamentalDegreeKernelDegreeWindowMulAction
      T hstable hbijective x₀
    IsCancelSMul (MonoidHom.ker (fundamentalDegree T x₀))
      (SectionalPath.DegreeWindow (T := T) x₀) := by
  letI := fundamentalDegreeKernelDegreeWindowMulAction
    T hstable hbijective x₀
  constructor
  intro g h X hgh
  apply Subtype.ext
  apply repetitionFundamentalGroup_smul_injective
    T hstable hbijective x₀ X.1
  exact congrArg Subtype.val hgh

include hstable hbijective in
/-- For a finite Riedtmann tree class, the order of the zero-degree deck
subgroup divides the number of tree vertices. -/
theorem fundamentalDegree_ker_natCard_dvd_tree_natCard
    [Finite (T.SectionalPath x₀)] :
    Nat.card (MonoidHom.ker (fundamentalDegree T x₀)) ∣
      Nat.card (T.SectionalPath x₀) := by
  let K := MonoidHom.ker (fundamentalDegree T x₀)
  let W := SectionalPath.DegreeWindow (T := T) x₀
  letI : Finite K := fundamentalDegree_ker_finite
    T hstable hbijective x₀
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (T.SectionalPath x₀) := Fintype.ofFinite _
  letI : MulAction K W := fundamentalDegreeKernelDegreeWindowMulAction
    T hstable hbijective x₀
  letI : IsCancelSMul K W := fundamentalDegreeKernelDegreeWindowIsCancelSMul
    T hstable hbijective x₀
  letI : Fintype W := SectionalPath.degreeWindowFintype (T := T) x₀
  have hdvd : Fintype.card K ∣ Fintype.card W :=
    card_group_dvd_card_of_isCancelSMul
  have hcard : Fintype.card W = Fintype.card (T.SectionalPath x₀) :=
    Fintype.card_congr (SectionalPath.degreeWindowEquiv (T := T) x₀).symm
  rw [hcard] at hdvd
  simpa only [Nat.card_eq_fintype_card] using hdvd

/-- The zero-degree deck subgroup acts on the finite window of edges from
degree zero to degree one. -/
@[reducible]
def fundamentalDegreeKernelDegreeZeroOneEdgeMulAction :
    MulAction (MonoidHom.ker (fundamentalDegree T x₀))
      (SectionalPath.DegreeZeroOneEdge (T := T) x₀) where
  smul g E :=
    ⟨⟨⟨repetitionDeckActVertex T hstable hbijective x₀ g.1 E.1.1.1, by
        have hdegree := repetitionDegree_deckActVertex
          T hstable hbijective x₀ g.1 E.1.1.1
        rw [g.2] at hdegree
        have hdegree' : SectionalPath.repetitionDegree (T := T) x₀
            (repetitionDeckActVertex T hstable hbijective x₀ g.1 E.1.1.1) =
            SectionalPath.repetitionDegree (T := T) x₀ E.1.1.1 := by
          simpa using hdegree
        rw [hdegree']
        exact E.1.1.2⟩,
      ⟨repetitionDeckActVertex T hstable hbijective x₀ g.1 E.1.2.1, by
        have hdegree := repetitionDegree_deckActVertex
          T hstable hbijective x₀ g.1 E.1.2.1
        rw [g.2] at hdegree
        have hdegree' : SectionalPath.repetitionDegree (T := T) x₀
            (repetitionDeckActVertex T hstable hbijective x₀ g.1 E.1.2.1) =
            SectionalPath.repetitionDegree (T := T) x₀ E.1.2.1 := by
          simpa using hdegree
        rw [hdegree']
        exact E.1.2.2⟩⟩, by
      rcases E.2 with ⟨a⟩
      exact ⟨(repetitionDeckPrefunctor
        T hstable hbijective x₀ g.1).map a⟩⟩
  one_smul E := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact repetitionDeckActVertex_one
        T hstable hbijective x₀ E.1.1.1
    · apply Subtype.ext
      exact repetitionDeckActVertex_one
        T hstable hbijective x₀ E.1.2.1
  mul_smul g h E := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact repetitionDeckActVertex_mul
        T hstable hbijective x₀ g.1 h.1 E.1.1.1
    · apply Subtype.ext
      exact repetitionDeckActVertex_mul
        T hstable hbijective x₀ g.1 h.1 E.1.2.1

/-- The zero-degree subgroup acts freely on the finite edge window. -/
theorem fundamentalDegreeKernelDegreeZeroOneEdgeIsCancelSMul :
    letI := fundamentalDegreeKernelDegreeZeroOneEdgeMulAction
      T hstable hbijective x₀
    IsCancelSMul (MonoidHom.ker (fundamentalDegree T x₀))
      (SectionalPath.DegreeZeroOneEdge (T := T) x₀) := by
  letI := fundamentalDegreeKernelDegreeZeroOneEdgeMulAction
    T hstable hbijective x₀
  constructor
  intro g h E hgh
  apply Subtype.ext
  apply repetitionFundamentalGroup_smul_injective
    T hstable hbijective x₀ E.1.1.1
  have hfirst := congrArg
    (fun F : SectionalPath.DegreeZeroOneEdge (T := T) x₀ ↦ F.1.1.1) hgh
  exact hfirst

include hstable hbijective in
/-- For a finite Riedtmann tree class, the order of the zero-degree deck
subgroup divides the number of edges in the canonical finite window. -/
theorem fundamentalDegree_ker_natCard_dvd_degreeZeroOneEdge_card
    [Finite (T.SectionalPath x₀)] :
    Nat.card (MonoidHom.ker (fundamentalDegree T x₀)) ∣
      Fintype.card (SectionalPath.DegreeZeroOneEdge (T := T) x₀) := by
  let K := MonoidHom.ker (fundamentalDegree T x₀)
  let E := SectionalPath.DegreeZeroOneEdge (T := T) x₀
  letI : Finite K := fundamentalDegree_ker_finite
    T hstable hbijective x₀
  letI : Fintype K := Fintype.ofFinite K
  letI : MulAction K E :=
    fundamentalDegreeKernelDegreeZeroOneEdgeMulAction
      T hstable hbijective x₀
  letI : IsCancelSMul K E :=
    fundamentalDegreeKernelDegreeZeroOneEdgeIsCancelSMul
      T hstable hbijective x₀
  letI : Fintype E := SectionalPath.degreeZeroOneEdgeFintype (T := T) x₀
  simpa only [Nat.card_eq_fintype_card] using
    (card_group_dvd_card_of_isCancelSMul :
      Fintype.card K ∣ Fintype.card E)

include hstable hbijective in
/-- For a finite Riedtmann tree class, the zero-degree deck subgroup is
trivial.  Its order divides both the number of tree vertices and the number
of tree edges, which differ by one. -/
theorem fundamentalDegree_ker_natCard_eq_one
    [Finite (T.SectionalPath x₀)] :
    Nat.card (MonoidHom.ker (fundamentalDegree T x₀)) = 1 := by
  have hvertices := fundamentalDegree_ker_natCard_dvd_tree_natCard
    T hstable hbijective x₀
  have hedges :=
    fundamentalDegree_ker_natCard_dvd_degreeZeroOneEdge_card
      T hstable hbijective x₀
  rw [← SectionalPath.card_degreeZeroOneEdge_add_one (T := T) x₀]
    at hvertices
  have hcoprime : Nat.Coprime
      (Fintype.card (SectionalPath.DegreeZeroOneEdge (T := T) x₀) + 1)
      (Fintype.card (SectionalPath.DegreeZeroOneEdge (T := T) x₀)) := by
    rw [Nat.coprime_self_add_left]
    simp
  exact Nat.eq_one_of_dvd_coprimes hcoprime hvertices hedges

include hstable hbijective in
/-- When the Riedtmann tree class is finite, integer degree detects every
element of the based fundamental group. -/
theorem fundamentalDegree_injective
    [Finite (T.SectionalPath x₀)] :
    Function.Injective (fundamentalDegree T x₀) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Subgroup.card_eq_one.mp
    (fundamentalDegree_ker_natCard_eq_one T hstable hbijective x₀)

include hstable hbijective in
/-- A stable translation quiver with finite Riedtmann sectional tree has free
based fundamental group: its degree map embeds it in the infinite cyclic
group, and Nielsen--Schreier applies to the image. -/
theorem fundamentalGroup_isFree_of_finite_sectionalTree
    [Finite (T.SectionalPath x₀)] :
    IsFreeGroup (FundamentalGroup T x₀) := by
  let f := fundamentalDegree T x₀
  letI : IsFreeGroup (Multiplicative ℤ) :=
    IsFreeGroup.ofMulEquiv
      (FreeGroup.mulEquivIntOfUnique :
        FreeGroup Unit ≃* Multiplicative ℤ)
  letI : IsFreeGroup f.range := inferInstance
  exact IsFreeGroup.ofMulEquiv
    (MonoidHom.ofInjective
      (fundamentalDegree_injective T hstable hbijective x₀)).symm

end RiedtmannCover
end MagnitudeConjecture.MeshCategory.RightMeshData
