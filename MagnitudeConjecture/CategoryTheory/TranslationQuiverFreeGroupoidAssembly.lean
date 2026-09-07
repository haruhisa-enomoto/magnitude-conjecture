import MagnitudeConjecture.CategoryTheory.TranslationQuiverHomotopyGroupoidPresentation
import MagnitudeConjecture.CategoryTheory.TranslationQuiverPeriodicComponent

/-!
# Free-groupoid assembly for finite translation quivers

The ambient mesh-homotopy groupoid is assembled from the homotopy groupoids
of its periodic stable components, the formal mesh edges in nonperiodic
tau-chains, and the unique projective-source arrow in each nonperiodic
sigma-strip.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.MeshCategory.RightMeshData.IsTauInjective

-- The augmented, homotopy-groupoid, and generator vertex types below are
-- transparent synonyms of their underlying quiver vertices.
set_option backward.isDefEq.respectTransparency false

universe u

variable {Q : Type u} [Quiver.{u} Q]
variable (T : RightMeshData Q) (hT : T.IsTauInjective)

open UniversalCover

/-- An arrow between periodic vertices keeps both endpoints in the same
periodic stable component. -/
theorem isInPeriodicComponent_target_of_arrow
    {E : PeriodicComponent T hT} {x y : Q}
    (hxE : IsInPeriodicComponent T hT E x)
    (hy : IsPeriodicVertex T y) (a : x ⟶ y) :
    IsInPeriodicComponent T hT E y := by
  let hx := hxE.choose
  let X : PeriodicTauOrbit T := ⟨tauClass T x,
    (isPeriodicTauOrbit_tauClass T x).2 hx⟩
  let Y : PeriodicTauOrbit T := ⟨tauClass T y,
    (isPeriodicTauOrbit_tauClass T y).2 hy⟩
  let e := arrowOrbitClass T hT a
  have hends := Sym2.eq_iff.mp
    (arrowOrbitEnds_eq_mk_source_target T hT e)
  have hXY : PeriodicAdjacent T hT X Y := by
    rcases hends with hends | hends
    · exact ⟨e, Or.inl ⟨hends.1.symm, hends.2.symm⟩⟩
    · exact ⟨e, Or.inr ⟨hends.2.symm, hends.1.symm⟩⟩
  refine ⟨hy, ?_⟩
  exact (periodicAdjacent_related T hT hXY).symm.trans hxE.choose_spec

/-- The augmented quiver of a periodic component includes into the ambient
augmented quiver. -/
def periodicComponentAugmentedInclusion
    (E : PeriodicComponent T hT) :
    AugmentedVertex (periodicComponentRightMeshData T hT E) ⥤q
      AugmentedVertex T where
  obj x := x.1
  map := by
    intro x y a
    cases a with
    | old a => exact AugmentedArrow.old a
    | mesh x =>
        exact AugmentedArrow.mesh
          ⟨x.1.1, periodicComponentVertex_not_projective T hT x.1⟩

theorem periodicComponentAugmentedInclusion_meshCompatible
    (E : PeriodicComponent T hT) :
    HomotopyGroupoid.MeshCompatible
      (periodicComponentRightMeshData T hT E)
      (periodicComponentAugmentedInclusion T hT E ⋙q
        HomotopyGroupoid.of T) := by
  intro s a
  let ambientSource : {x : Q // x ∉ T.projective} :=
    ⟨s.1.1, periodicComponentVertex_not_projective T hT s.1⟩
  let ambientMeshArrow : T.MeshArrow ambientSource :=
    ⟨a.1.1, a.2⟩
  exact HomotopyGroupoid.of_mesh_eq_old_comp_old
    T ambientSource ambientMeshArrow

/-- Inclusion of a periodic component descends through mesh homotopy to the
ambient mesh-homotopy groupoid. -/
def periodicComponentHomotopyInclusion
    (E : PeriodicComponent T hT) :
    HomotopyGroupoid (periodicComponentRightMeshData T hT E) ⥤
      HomotopyGroupoid T :=
  HomotopyGroupoid.lift
    (periodicComponentRightMeshData T hT E)
    (periodicComponentAugmentedInclusion T hT E ⋙q
      HomotopyGroupoid.of T)
    (periodicComponentAugmentedInclusion_meshCompatible T hT E)

@[simp]
theorem periodicComponentHomotopyInclusion_map_augmented
    (E : PeriodicComponent T hT)
    {x y : AugmentedVertex (periodicComponentRightMeshData T hT E)}
    (a : x ⟶ y) :
    (periodicComponentHomotopyInclusion T hT E).map
        ((HomotopyGroupoid.of
          (periodicComponentRightMeshData T hT E)).map a) =
      (HomotopyGroupoid.of T).map
        ((periodicComponentAugmentedInclusion T hT E).map a) :=
  HomotopyGroupoid.lift_map_of
    (periodicComponentRightMeshData T hT E)
    (periodicComponentAugmentedInclusion T hT E ⋙q
      HomotopyGroupoid.of T)
    (periodicComponentAugmentedInclusion_meshCompatible T hT E) a

section Generators

variable [Finite Q]
variable [periodicFree : ∀ E : PeriodicComponent T hT,
  IsFreeGroupoid
    (HomotopyGroupoid (periodicComponentRightMeshData T hT E))]

/-- Generators retained after eliminating the nonperiodic mesh relations:
formal mesh edges on nonperiodic tau-chains, projective-source boundary
arrows of nonperiodic sigma-strips, and the chosen free generators internal
to every periodic stable component. -/
inductive GlobalGenerator : Q → Q → Type u
  | nonperiodicMesh (x : Q) (hx : ¬ IsPeriodicVertex T x)
      (hxp : x ∉ T.projective) :
      GlobalGenerator x (T.tau ⟨x, hxp⟩)
  | boundary {x y : Q} (a : x ⟶ y) (hxp : x ∈ T.projective)
      (hxy : ¬ (IsPeriodicVertex T x ∧ IsPeriodicVertex T y)) :
      GlobalGenerator x y
  | periodic (E : PeriodicComponent T hT)
      {x y : IsFreeGroupoid.Generators
        (HomotopyGroupoid (periodicComponentRightMeshData T hT E))}
      (g : x ⟶ y) :
      GlobalGenerator
        (show Q from (show PeriodicComponentVertex T hT E from x).1)
        (show Q from (show PeriodicComponentVertex T hT E from y).1)

/-- Interpret a retained global generator in the ambient mesh-homotopy
groupoid. -/
def globalGeneratorMorphism {x y : Q}
    (g : GlobalGenerator T hT x y) :
    ((show HomotopyGroupoid T from x) ⟶
      (show HomotopyGroupoid T from y)) := by
  cases g with
  | nonperiodicMesh x hx hxp =>
      exact (HomotopyGroupoid.of T).map
        (AugmentedArrow.mesh ⟨x, hxp⟩)
  | boundary a hxp hxy =>
      exact (HomotopyGroupoid.of T).map (AugmentedArrow.old a)
  | periodic E g =>
      exact (periodicComponentHomotopyInclusion T hT E).map
        (IsFreeGroupoid.of g)

section Extension

variable {X : Type u} [Group X]
variable (f : ∀ {x y : Q}, GlobalGenerator T hT x y → X)

/-- Restrict a global generator labelling to the chosen free generators of
one periodic stable component. -/
def periodicGeneratorLabel (E : PeriodicComponent T hT) :
    Quiver.Labelling
      (IsFreeGroupoid.Generators
        (HomotopyGroupoid (periodicComponentRightMeshData T hT E))) X :=
  fun {_ _} g ↦ f (GlobalGenerator.periodic E g)

/-- The unique functor on one free periodic component induced by a global
generator labelling. -/
noncomputable def periodicLabelFunctor (E : PeriodicComponent T hT) :
    HomotopyGroupoid (periodicComponentRightMeshData T hT E) ⥤
      CategoryTheory.SingleObj X :=
  Classical.choose
    (IsFreeGroupoid.unique_lift
      (periodicGeneratorLabel T hT (f := f) E))

omit [Finite Q] in
theorem periodicLabelFunctor_map_generator
    (E : PeriodicComponent T hT)
    {x y : IsFreeGroupoid.Generators
      (HomotopyGroupoid (periodicComponentRightMeshData T hT E))}
    (g : x ⟶ y) :
    (periodicLabelFunctor T hT (f := f) E).map (IsFreeGroupoid.of g) =
      f (GlobalGenerator.periodic E g) :=
  (Classical.choose_spec
    (IsFreeGroupoid.unique_lift
      (periodicGeneratorLabel T hT (f := f) E))).1 x y g

/-- The periodic component containing a periodic vertex. -/
def periodicComponentOfVertex (x : Q) (hx : IsPeriodicVertex T x) :
    PeriodicComponent T hT :=
  periodicComponentClass T hT
    ⟨tauClass T x, (isPeriodicTauOrbit_tauClass T x).2 hx⟩

/-- A periodic vertex, regarded as a vertex of its own periodic component. -/
def periodicVertexInOwnComponent (x : Q) (hx : IsPeriodicVertex T x) :
    PeriodicComponentVertex T hT (periodicComponentOfVertex T hT x hx) :=
  ⟨x, hx, rfl⟩

/-- Label an ambient formal mesh edge.  A periodic source is evaluated by
the functor on its periodic component; a nonperiodic source is one of the
retained global generators. -/
noncomputable def globalMeshLabel
    (s : {x : Q // x ∉ T.projective}) : X := by
  classical
  by_cases hx : IsPeriodicVertex T s.1
  · let E := periodicComponentOfVertex T hT s.1 hx
    let xE := periodicVertexInOwnComponent T hT s.1 hx
    let D := periodicComponentRightMeshData T hT E
    let sxE : {x : PeriodicComponentVertex T hT E //
        x ∉ D.projective} := ⟨xE, by simp [D,
      periodicComponentRightMeshData_projective]⟩
    exact (periodicLabelFunctor T hT (f := f) E).map
      ((HomotopyGroupoid.of D).map (AugmentedArrow.mesh sxE))
  · exact f (GlobalGenerator.nonperiodicMesh s.1 hx s.2)

/-- Label an ordinary arrow whose two endpoints are periodic by evaluating it
inside their common periodic stable component. -/
noncomputable def periodicOldLabel
    {x y : Q} (a : x ⟶ y)
    (hx : IsPeriodicVertex T x) (hy : IsPeriodicVertex T y) : X := by
  let E := periodicComponentOfVertex T hT x hx
  let xE := periodicVertexInOwnComponent T hT x hx
  let yE : PeriodicComponentVertex T hT E :=
    ⟨y, isInPeriodicComponent_target_of_arrow T hT xE.2 hy a⟩
  let D := periodicComponentRightMeshData T hT E
  exact (periodicLabelFunctor T hT (f := f) E).map
    ((HomotopyGroupoid.of D).map
      (AugmentedArrow.old (show xE ⟶ yE from a)))

omit [Finite Q] in
theorem periodicOldLabel_eq_of_component
    (E : PeriodicComponent T hT)
    (x y : PeriodicComponentVertex T hT E) (a : x ⟶ y) :
    periodicOldLabel T hT (f := f) a
        (periodicComponentVertex_isPeriodic T hT x)
        (periodicComponentVertex_isPeriodic T hT y) =
      (periodicLabelFunctor T hT (f := f) E).map
        ((HomotopyGroupoid.of
          (periodicComponentRightMeshData T hT E)).map
            (AugmentedArrow.old a)) := by
  rcases x with ⟨x, hx, rfl⟩
  rcases y with ⟨y, hyE⟩
  unfold periodicOldLabel
  rfl

omit [Finite Q] in
theorem globalMeshLabel_eq_of_periodicComponentVertex
    (E : PeriodicComponent T hT)
    (x : PeriodicComponentVertex T hT E) :
    globalMeshLabel T hT (f := f)
        ⟨x.1, periodicComponentVertex_not_projective T hT x⟩ =
      (periodicLabelFunctor T hT (f := f) E).map
        ((HomotopyGroupoid.of
          (periodicComponentRightMeshData T hT E)).map
            (AugmentedArrow.mesh
              (⟨x, by simp [periodicComponentRightMeshData_projective]⟩ :
                {z : PeriodicComponentVertex T hT E //
                  z ∉ (periodicComponentRightMeshData T hT E).projective}))) := by
  rcases x with ⟨x, hx, rfl⟩
  rw [globalMeshLabel]
  simp only [hx, ↓reduceDIte]
  rfl

/-- Recursively label an ordinary arrow in a nonperiodic sigma-strip.  At the
projective boundary it is a retained generator; before the boundary it is
solved from the mesh relation and the next polarized arrow. -/
private noncomputable def nonperiodicOldLabel
    (a : NonperiodicArrow T) : X := by
  by_cases hsource : a.1.1 ∈ T.projective
  · exact f (GlobalGenerator.boundary a.1.2.2 hsource a.2)
  · exact (nonperiodicOldLabel
      (nonperiodicArrowForward T hT a hsource))⁻¹ *
        globalMeshLabel T hT (f := f) ⟨a.1.1, hsource⟩
termination_by sigmaBoundaryDistance T hT a.2
decreasing_by
  have hstep :=
    nonperiodicArrowForward_distance_add_one T hT a hsource
  omega

/-- Label any ambient ordinary arrow, using the periodic component functor or
the nonperiodic sigma-strip recursion as appropriate. -/
noncomputable def globalOldLabel {x y : Q} (a : x ⟶ y) : X := by
  classical
  by_cases hxy : IsPeriodicVertex T x ∧ IsPeriodicVertex T y
  · exact periodicOldLabel T hT (f := f) a hxy.1 hxy.2
  · exact nonperiodicOldLabel T hT (f := f)
      (⟨(⟨x, y, a⟩ : Arrow T), hxy⟩ : NonperiodicArrow T)

omit [Finite Q] in
theorem globalMeshLabel_of_nonperiodic
    (s : {x : Q // x ∉ T.projective})
    (hs : ¬ IsPeriodicVertex T s.1) :
    globalMeshLabel T hT (f := f) s =
      f (GlobalGenerator.nonperiodicMesh s.1 hs s.2) := by
  rw [globalMeshLabel]
  simp only [hs, ↓reduceDIte]

private theorem nonperiodicOldLabel_of_projective
    (a : NonperiodicArrow T) (ha : a.1.1 ∈ T.projective) :
    nonperiodicOldLabel T hT (f := f) a =
      f (GlobalGenerator.boundary a.1.2.2 ha a.2) := by
  rw [nonperiodicOldLabel]
  simp only [ha, ↓reduceDIte]

private theorem nonperiodicOldLabel_of_nonprojective
    (a : NonperiodicArrow T) (ha : a.1.1 ∉ T.projective) :
    nonperiodicOldLabel T hT (f := f) a =
      (nonperiodicOldLabel T hT (f := f)
        (nonperiodicArrowForward T hT a ha))⁻¹ *
          globalMeshLabel T hT (f := f) ⟨a.1.1, ha⟩ := by
  rw [nonperiodicOldLabel]
  simp only [ha, ↓reduceDIte]

theorem globalOldLabel_of_nonperiodic
    {x y : Q} (a : x ⟶ y)
    (hxy : ¬ (IsPeriodicVertex T x ∧ IsPeriodicVertex T y)) :
    globalOldLabel T hT (f := f) a =
      nonperiodicOldLabel T hT (f := f)
        (⟨(⟨x, y, a⟩ : Arrow T), hxy⟩ : NonperiodicArrow T) := by
  rw [globalOldLabel]
  simp only [hxy, ↓reduceDIte]

theorem globalOldLabel_of_periodic
    {x y : Q} (a : x ⟶ y)
    (hx : IsPeriodicVertex T x) (hy : IsPeriodicVertex T y) :
    globalOldLabel T hT (f := f) a =
      periodicOldLabel T hT (f := f) a hx hy := by
  rw [globalOldLabel]
  simp only [hx, hy, and_self, ↓reduceDIte]

/-- The augmented-quiver labelling determined by retained global
generators. -/
noncomputable def globalAugmentedLabel :
    AugmentedVertex T ⥤q CategoryTheory.SingleObj X where
  obj _ := ()
  map := by
    intro x y a
    cases a with
    | old a => exact globalOldLabel T hT (f := f) a
    | mesh s => exact globalMeshLabel T hT (f := f) s

theorem globalAugmentedLabel_meshCompatible_of_endpoint_nonperiodic
    (s : {x : Q // x ∉ T.projective})
    (a : T.MeshArrow s)
    (hxy : ¬ (IsPeriodicVertex T s.1 ∧ IsPeriodicVertex T a.1)) :
    (globalAugmentedLabel T hT (f := f)).map
        (AugmentedArrow.mesh s) =
      (globalAugmentedLabel T hT (f := f)).map
          (AugmentedArrow.old a.2) ≫
        (globalAugmentedLabel T hT (f := f)).map
          (AugmentedArrow.old ((T.arrowEquiv s a.1) a.2)) := by
  let na : NonperiodicArrow T :=
    ⟨(⟨s.1, a.1, a.2⟩ : Arrow T), hxy⟩
  let hforward := arrowTranslation_endpoint_nonperiodic T hxy s.2
  have hforwardArrow :
      nonperiodicArrowForward T hT na s.2 =
        (⟨(⟨a.1, T.tau s, (T.arrowEquiv s a.1) a.2⟩ : Arrow T),
          hforward⟩ : NonperiodicArrow T) := by
    apply Subtype.ext
    rfl
  rw [show (globalAugmentedLabel T hT (f := f)).map
      (AugmentedArrow.mesh s) = globalMeshLabel T hT (f := f) s by rfl]
  rw [show (globalAugmentedLabel T hT (f := f)).map
      (AugmentedArrow.old a.2) = globalOldLabel T hT (f := f) a.2 by rfl]
  rw [show (globalAugmentedLabel T hT (f := f)).map
      (AugmentedArrow.old ((T.arrowEquiv s a.1) a.2)) =
        globalOldLabel T hT (f := f) ((T.arrowEquiv s a.1) a.2) by rfl]
  change globalMeshLabel T hT (f := f) s =
    globalOldLabel T hT (f := f) ((T.arrowEquiv s a.1) a.2) *
      globalOldLabel T hT (f := f) a.2
  rw [globalOldLabel_of_nonperiodic T hT f a.2 hxy,
    globalOldLabel_of_nonperiodic T hT f
      ((T.arrowEquiv s a.1) a.2) hforward]
  rw [nonperiodicOldLabel_of_nonprojective T hT f na s.2]
  rw [hforwardArrow]
  simp only [mul_inv_cancel_left]
  rfl

theorem globalAugmentedLabel_meshCompatible_of_endpoint_periodic
    (s : {x : Q // x ∉ T.projective})
    (a : T.MeshArrow s)
    (hx : IsPeriodicVertex T s.1) (hy : IsPeriodicVertex T a.1) :
    (globalAugmentedLabel T hT (f := f)).map
        (AugmentedArrow.mesh s) =
      (globalAugmentedLabel T hT (f := f)).map
          (AugmentedArrow.old a.2) ≫
        (globalAugmentedLabel T hT (f := f)).map
          (AugmentedArrow.old ((T.arrowEquiv s a.1) a.2)) := by
  let E := periodicComponentOfVertex T hT s.1 hx
  let xE := periodicVertexInOwnComponent T hT s.1 hx
  let yE : PeriodicComponentVertex T hT E :=
    ⟨a.1, isInPeriodicComponent_target_of_arrow T hT xE.2 hy a.2⟩
  let D := periodicComponentRightMeshData T hT E
  let sxE : {x : PeriodicComponentVertex T hT E //
      x ∉ D.projective} := ⟨xE, by simp [D,
    periodicComponentRightMeshData_projective]⟩
  let txE := D.tau sxE
  let localMesh : D.MeshArrow sxE := ⟨yE, a.2⟩
  let b : yE ⟶ txE := (D.arrowEquiv sxE yE) a.2
  let F := periodicLabelFunctor T hT (f := f) E
  have hlocal := congrArg F.map
    (HomotopyGroupoid.of_mesh_eq_old_comp_old D sxE localMesh)
  rw [F.map_comp] at hlocal
  change
    F.map ((HomotopyGroupoid.of D).map (AugmentedArrow.mesh sxE)) =
      F.map ((HomotopyGroupoid.of D).map (AugmentedArrow.old b)) *
        F.map ((HomotopyGroupoid.of D).map
          (AugmentedArrow.old (show xE ⟶ yE from a.2))) at hlocal
  rw [show (globalAugmentedLabel T hT (f := f)).map
      (AugmentedArrow.mesh s) = globalMeshLabel T hT (f := f) s by rfl]
  rw [show (globalAugmentedLabel T hT (f := f)).map
      (AugmentedArrow.old a.2) = globalOldLabel T hT (f := f) a.2 by rfl]
  rw [show (globalAugmentedLabel T hT (f := f)).map
      (AugmentedArrow.old ((T.arrowEquiv s a.1) a.2)) =
        globalOldLabel T hT (f := f) ((T.arrowEquiv s a.1) a.2) by rfl]
  change globalMeshLabel T hT (f := f) s =
    globalOldLabel T hT (f := f) ((T.arrowEquiv s a.1) a.2) *
      globalOldLabel T hT (f := f) a.2
  rw [show globalMeshLabel T hT (f := f) s =
      globalMeshLabel T hT (f := f)
        ⟨xE.1, periodicComponentVertex_not_projective T hT xE⟩ by rfl]
  rw [globalMeshLabel_eq_of_periodicComponentVertex T hT f E xE]
  rw [globalOldLabel_of_periodic T hT f a.2 hx hy]
  rw [show periodicOldLabel T hT (f := f) a.2 hx hy =
      periodicOldLabel T hT (f := f) (show xE ⟶ yE from a.2)
        (periodicComponentVertex_isPeriodic T hT xE)
        (periodicComponentVertex_isPeriodic T hT yE) by rfl]
  rw [periodicOldLabel_eq_of_component T hT f E xE yE a.2]
  let htx := periodicComponentVertex_isPeriodic T hT txE
  rw [globalOldLabel_of_periodic T hT f
    ((T.arrowEquiv s a.1) a.2) hy htx]
  rw [show periodicOldLabel T hT (f := f)
      ((T.arrowEquiv s a.1) a.2) hy htx =
        periodicOldLabel T hT (f := f) b
          (periodicComponentVertex_isPeriodic T hT yE)
          (periodicComponentVertex_isPeriodic T hT txE) by rfl]
  rw [periodicOldLabel_eq_of_component T hT f E yE txE b]
  exact hlocal

/-- The global augmented labelling satisfies every polarized mesh relation. -/
theorem globalAugmentedLabel_meshCompatible :
    HomotopyGroupoid.MeshCompatible T
      (globalAugmentedLabel T hT (f := f)) := by
  intro s a
  by_cases hxy :
      IsPeriodicVertex T s.1 ∧ IsPeriodicVertex T a.1
  · exact globalAugmentedLabel_meshCompatible_of_endpoint_periodic
      T hT f s a hxy.1 hxy.2
  · exact globalAugmentedLabel_meshCompatible_of_endpoint_nonperiodic
      T hT f s a hxy

/-- The functor from the ambient mesh-homotopy groupoid determined by a
labelling of the retained global generators. -/
noncomputable def globalLabelFunctor :
    HomotopyGroupoid T ⥤ CategoryTheory.SingleObj X :=
  HomotopyGroupoid.lift T
    (globalAugmentedLabel T hT (f := f))
    (globalAugmentedLabel_meshCompatible T hT f)

@[simp]
theorem globalLabelFunctor_map_augmented
    {x y : AugmentedVertex T} (a : x ⟶ y) :
    (globalLabelFunctor T hT (f := f)).map
        ((HomotopyGroupoid.of T).map a) =
      (globalAugmentedLabel T hT (f := f)).map a :=
  HomotopyGroupoid.lift_map_of T
    (globalAugmentedLabel T hT (f := f))
    (globalAugmentedLabel_meshCompatible T hT f) a

/-- On a periodic stable component, the global extension has the same value
on every morphism as the unique functor supplied by that component's
free-groupoid structure. -/
theorem globalLabelFunctor_map_periodicComponent
    (E : PeriodicComponent T hT)
    {x y : HomotopyGroupoid
      (periodicComponentRightMeshData T hT E)} (p : x ⟶ y) :
    (globalLabelFunctor T hT (f := f)).map
        ((periodicComponentHomotopyInclusion T hT E).map p) =
      (periodicLabelFunctor T hT (f := f) E).map p := by
  let D := periodicComponentRightMeshData T hT E
  let G := periodicComponentHomotopyInclusion T hT E ⋙
    globalLabelFunctor T hT (f := f)
  let P := periodicLabelFunctor T hT (f := f) E
  let eta : G ⟶ P := HomotopyGroupoid.natTransOfGenerator D G P
      (fun _ ↦ (1 : X)) (by
    intro x y a
    change (1 : X) * G.map ((HomotopyGroupoid.of D).map a) =
      P.map ((HomotopyGroupoid.of D).map a) * (1 : X)
    simp only [one_mul, mul_one]
    cases a with
    | old a =>
        change (globalLabelFunctor T hT (f := f)).map
            ((periodicComponentHomotopyInclusion T hT E).map
              ((HomotopyGroupoid.of D).map
                (AugmentedArrow.old a))) =
          P.map ((HomotopyGroupoid.of D).map
            (AugmentedArrow.old a))
        rw [periodicComponentHomotopyInclusion_map_augmented,
          globalLabelFunctor_map_augmented]
        change globalOldLabel T hT (f := f) a =
          P.map ((HomotopyGroupoid.of D).map
            (AugmentedArrow.old a))
        rw [globalOldLabel_of_periodic T hT f a
          (periodicComponentVertex_isPeriodic T hT x)
          (periodicComponentVertex_isPeriodic T hT y)]
        exact periodicOldLabel_eq_of_component T hT f E x y a
    | mesh s =>
        change (globalLabelFunctor T hT (f := f)).map
            ((periodicComponentHomotopyInclusion T hT E).map
              ((HomotopyGroupoid.of D).map
                (AugmentedArrow.mesh s))) =
          P.map ((HomotopyGroupoid.of D).map
            (AugmentedArrow.mesh s))
        rw [periodicComponentHomotopyInclusion_map_augmented,
          globalLabelFunctor_map_augmented]
        change globalMeshLabel T hT (f := f)
            ⟨s.1.1, periodicComponentVertex_not_projective T hT s.1⟩ =
          P.map ((HomotopyGroupoid.of D).map
            (AugmentedArrow.mesh s))
        exact globalMeshLabel_eq_of_periodicComponentVertex
          T hT f E s.1)
  have hp := eta.naturality p
  change (1 : X) * G.map p = P.map p * (1 : X) at hp
  have hp' : G.map p = P.map p := by
    simpa only [one_mul, mul_one] using hp
  change (show X from (globalLabelFunctor T hT (f := f)).map
      ((periodicComponentHomotopyInclusion T hT E).map p)) =
    (show X from (periodicLabelFunctor T hT (f := f) E).map p)
  exact hp'

omit [Finite Q] in
/-- Any functor with the prescribed values on retained generators restricts
to the prescribed functor on every periodic component. -/
theorem periodicComponent_comp_eq_periodicLabelFunctor
    (H : HomotopyGroupoid T ⥤ CategoryTheory.SingleObj X)
    (hH : ∀ {x y : Q} (g : GlobalGenerator T hT x y),
      H.map (globalGeneratorMorphism T hT g) = f g)
    (E : PeriodicComponent T hT) :
    periodicComponentHomotopyInclusion T hT E ⋙ H =
      periodicLabelFunctor T hT (f := f) E := by
  apply IsFreeGroupoid.ext_functor
  intro x y g
  change H.map ((periodicComponentHomotopyInclusion T hT E).map
      (IsFreeGroupoid.of g)) =
    (periodicLabelFunctor T hT (f := f) E).map
      (IsFreeGroupoid.of g)
  rw [show (periodicComponentHomotopyInclusion T hT E).map
      (IsFreeGroupoid.of g) =
        globalGeneratorMorphism T hT
          (GlobalGenerator.periodic E g) by rfl]
  rw [hH, periodicLabelFunctor_map_generator T hT f]

omit [Finite Q] in
/-- Such a functor has the prescribed value on every formal mesh edge. -/
theorem map_mesh_eq_globalMeshLabel
    (H : HomotopyGroupoid T ⥤ CategoryTheory.SingleObj X)
    (hH : ∀ {x y : Q} (g : GlobalGenerator T hT x y),
      H.map (globalGeneratorMorphism T hT g) = f g)
    (s : {x : Q // x ∉ T.projective}) :
    H.map ((HomotopyGroupoid.of T).map (AugmentedArrow.mesh s)) =
      globalMeshLabel T hT (f := f) s := by
  classical
  by_cases hx : IsPeriodicVertex T s.1
  · let E := periodicComponentOfVertex T hT s.1 hx
    let xE := periodicVertexInOwnComponent T hT s.1 hx
    let D := periodicComponentRightMeshData T hT E
    let sxE : {x : PeriodicComponentVertex T hT E //
        x ∉ D.projective} := ⟨xE, by simp [D,
      periodicComponentRightMeshData_projective]⟩
    have hcomponent := periodicComponent_comp_eq_periodicLabelFunctor
      T hT f H hH E
    change (periodicComponentHomotopyInclusion T hT E ⋙ H).map
        ((HomotopyGroupoid.of D).map
          (AugmentedArrow.mesh sxE)) =
      globalMeshLabel T hT (f := f)
        ⟨xE.1, periodicComponentVertex_not_projective T hT xE⟩
    rw [hcomponent]
    exact (globalMeshLabel_eq_of_periodicComponentVertex
      T hT f E xE).symm
  · rw [globalMeshLabel_of_nonperiodic T hT f s hx]
    exact hH (GlobalGenerator.nonperiodicMesh s.1 hx s.2)

omit [Finite Q] in
/-- On an ordinary arrow internal to a periodic component, any extension has
the prescribed periodic-component value. -/
theorem map_old_eq_periodicOldLabel
    (H : HomotopyGroupoid T ⥤ CategoryTheory.SingleObj X)
    (hH : ∀ {x y : Q} (g : GlobalGenerator T hT x y),
      H.map (globalGeneratorMorphism T hT g) = f g)
    {x y : Q} (a : x ⟶ y)
    (hx : IsPeriodicVertex T x) (hy : IsPeriodicVertex T y) :
    H.map ((HomotopyGroupoid.of T).map (AugmentedArrow.old a)) =
      periodicOldLabel T hT (f := f) a hx hy := by
  let E := periodicComponentOfVertex T hT x hx
  let xE := periodicVertexInOwnComponent T hT x hx
  let yE : PeriodicComponentVertex T hT E :=
    ⟨y, isInPeriodicComponent_target_of_arrow T hT xE.2 hy a⟩
  let D := periodicComponentRightMeshData T hT E
  have hcomponent := periodicComponent_comp_eq_periodicLabelFunctor
    T hT f H hH E
  change (periodicComponentHomotopyInclusion T hT E ⋙ H).map
      ((HomotopyGroupoid.of D).map
        (AugmentedArrow.old (show xE ⟶ yE from a))) =
    periodicOldLabel T hT (f := f) a hx hy
  rw [hcomponent]
  exact (periodicOldLabel_eq_of_component T hT f E xE yE a).symm

/-- The mesh relation forces any extension to obey the same terminating
normal-form recursion on a nonperiodic sigma-strip. -/
private theorem map_old_eq_nonperiodicOldLabel
    (H : HomotopyGroupoid T ⥤ CategoryTheory.SingleObj X)
    (hH : ∀ {x y : Q} (g : GlobalGenerator T hT x y),
      H.map (globalGeneratorMorphism T hT g) = f g)
    (a : NonperiodicArrow T) :
    H.map ((HomotopyGroupoid.of T).map
        (AugmentedArrow.old a.1.2.2)) =
      nonperiodicOldLabel T hT (f := f) a := by
  by_cases hsource : a.1.1 ∈ T.projective
  · rw [nonperiodicOldLabel_of_projective T hT f a hsource]
    exact hH (GlobalGenerator.boundary a.1.2.2 hsource a.2)
  · let s : {x : Q // x ∉ T.projective} := ⟨a.1.1, hsource⟩
    let meshA : T.MeshArrow s := ⟨a.1.2.1, a.1.2.2⟩
    let b := nonperiodicArrowForward T hT a hsource
    have ih := map_old_eq_nonperiodicOldLabel H hH b
    have hmesh := map_mesh_eq_globalMeshLabel T hT f H hH s
    have hrel := congrArg H.map
      (HomotopyGroupoid.of_mesh_eq_old_comp_old T s meshA)
    rw [H.map_comp] at hrel
    change H.map ((HomotopyGroupoid.of T).map
        (AugmentedArrow.mesh s)) =
      H.map ((HomotopyGroupoid.of T).map
          (AugmentedArrow.old b.1.2.2)) *
        H.map ((HomotopyGroupoid.of T).map
          (AugmentedArrow.old a.1.2.2)) at hrel
    rw [ih] at hrel
    have hvalue : globalMeshLabel T hT (f := f) s =
        nonperiodicOldLabel T hT (f := f) b *
          H.map ((HomotopyGroupoid.of T).map
            (AugmentedArrow.old a.1.2.2)) :=
      hmesh.symm.trans hrel
    rw [nonperiodicOldLabel_of_nonprojective T hT f a hsource]
    change H.map ((HomotopyGroupoid.of T).map
        (AugmentedArrow.old a.1.2.2)) =
      (nonperiodicOldLabel T hT (f := f) b)⁻¹ *
        globalMeshLabel T hT (f := f) s
    rw [hvalue]
    simp only [inv_mul_cancel_left]
termination_by sigmaBoundaryDistance T hT a.2
decreasing_by
  have hstep :=
    nonperiodicArrowForward_distance_add_one T hT a hsource
  omega

/-- Any extension has the prescribed value on every ordinary arrow. -/
theorem map_old_eq_globalOldLabel
    (H : HomotopyGroupoid T ⥤ CategoryTheory.SingleObj X)
    (hH : ∀ {x y : Q} (g : GlobalGenerator T hT x y),
      H.map (globalGeneratorMorphism T hT g) = f g)
    {x y : Q} (a : x ⟶ y) :
    H.map ((HomotopyGroupoid.of T).map (AugmentedArrow.old a)) =
      globalOldLabel T hT (f := f) a := by
  by_cases hxy : IsPeriodicVertex T x ∧ IsPeriodicVertex T y
  · rw [globalOldLabel_of_periodic T hT f a hxy.1 hxy.2]
    exact map_old_eq_periodicOldLabel T hT f H hH a hxy.1 hxy.2
  · rw [globalOldLabel_of_nonperiodic T hT f a hxy]
    exact map_old_eq_nonperiodicOldLabel T hT f H hH
      (⟨(⟨x, y, a⟩ : Arrow T), hxy⟩ : NonperiodicArrow T)

/-- The prescribed generator values determine a functor out of the ambient
mesh-homotopy groupoid uniquely. -/
theorem eq_globalLabelFunctor
    (H : HomotopyGroupoid T ⥤ CategoryTheory.SingleObj X)
    (hH : ∀ {x y : Q} (g : GlobalGenerator T hT x y),
      H.map (globalGeneratorMorphism T hT g) = f g) :
    H = globalLabelFunctor T hT (f := f) := by
  let F := globalLabelFunctor T hT (f := f)
  let eta : H ⟶ F := HomotopyGroupoid.natTransOfGenerator T H F
      (fun _ ↦ (1 : X)) (by
    intro x y a
    change (1 : X) * H.map ((HomotopyGroupoid.of T).map a) =
      F.map ((HomotopyGroupoid.of T).map a) * (1 : X)
    simp only [one_mul, mul_one]
    cases a with
    | old a =>
        rw [map_old_eq_globalOldLabel T hT f H hH a,
          globalLabelFunctor_map_augmented]
        rfl
    | mesh s =>
        rw [map_mesh_eq_globalMeshLabel T hT f H hH s,
          globalLabelFunctor_map_augmented]
        rfl)
  fapply CategoryTheory.Functor.hext
  · intro x
    exact Subsingleton.elim _ _
  · intro x y p
    apply heq_of_eq
    have hp := eta.naturality p
    change (1 : X) * H.map p = F.map p * (1 : X) at hp
    simpa only [one_mul, mul_one] using hp

/-- The constructed global functor takes each retained generator to its
assigned label. -/
theorem globalLabelFunctor_map_generator
    {x y : Q} (g : GlobalGenerator T hT x y) :
    (globalLabelFunctor T hT (f := f)).map
        (globalGeneratorMorphism T hT g) = f g := by
  cases g with
  | nonperiodicMesh x hx hxp =>
      change (globalLabelFunctor T hT (f := f)).map
          ((HomotopyGroupoid.of T).map
            (AugmentedArrow.mesh ⟨x, hxp⟩)) =
        f (GlobalGenerator.nonperiodicMesh x hx hxp)
      rw [globalLabelFunctor_map_augmented]
      exact globalMeshLabel_of_nonperiodic T hT f ⟨x, hxp⟩ hx
  | boundary a hxp hxy =>
      change (globalLabelFunctor T hT (f := f)).map
          ((HomotopyGroupoid.of T).map (AugmentedArrow.old a)) =
        f (GlobalGenerator.boundary a hxp hxy)
      rw [globalLabelFunctor_map_augmented]
      change globalOldLabel T hT (f := f) a =
        f (GlobalGenerator.boundary a hxp hxy)
      rw [globalOldLabel_of_nonperiodic T hT f a hxy]
      exact nonperiodicOldLabel_of_projective T hT f
        (⟨(⟨_, _, a⟩ : Arrow T), hxy⟩ : NonperiodicArrow T) hxp
  | periodic E g =>
      change (globalLabelFunctor T hT (f := f)).map
          ((periodicComponentHomotopyInclusion T hT E).map
            (IsFreeGroupoid.of g)) =
        f (GlobalGenerator.periodic E g)
      rw [globalLabelFunctor_map_periodicComponent T hT f E
        (IsFreeGroupoid.of g)]
      exact periodicLabelFunctor_map_generator T hT f E g

end Extension

/-- If every periodic stable component has a free mesh-homotopy groupoid,
then the full mesh-homotopy groupoid is free.  Nonperiodic tau-chains and
sigma-strips contribute respectively their formal mesh edges and their unique
projective-source boundary arrows. -/
@[reducible] noncomputable def isFreeGroupoidOfPeriodicComponents :
    IsFreeGroupoid (HomotopyGroupoid T) := by
  let generators :
      Quiver (IsFreeGroupoid.Generators (HomotopyGroupoid T)) :=
    ⟨fun x y ↦ GlobalGenerator T hT (show Q from x) (show Q from y)⟩
  let ofGenerator : ∀
      {x y : IsFreeGroupoid.Generators (HomotopyGroupoid T)},
      @Quiver.Hom _ generators x y →
        ((show HomotopyGroupoid T from x) ⟶
          (show HomotopyGroupoid T from y)) :=
    fun {_ _} g ↦ globalGeneratorMorphism T hT g
  refine {
    quiverGenerators := generators
    of := ofGenerator
    unique_lift := ?_ }
  intro X _ label
  let f : ∀ {x y : Q}, GlobalGenerator T hT x y → X :=
    fun {_ _} g ↦ label g
  let F := globalLabelFunctor T hT (f := f)
  refine ⟨F, ?_, ?_⟩
  · intro x y g
    change F.map (globalGeneratorMorphism T hT g) = label g
    exact globalLabelFunctor_map_generator T hT f g
  · intro H hH
    apply eq_globalLabelFunctor T hT f H
    intro x y g
    change H.map (ofGenerator g) = f g
    exact hH (show IsFreeGroupoid.Generators (HomotopyGroupoid T) from x)
      (show IsFreeGroupoid.Generators (HomotopyGroupoid T) from y) g

end Generators

end MagnitudeConjecture.MeshCategory.RightMeshData.IsTauInjective
