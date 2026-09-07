import MagnitudeConjecture.CategoryTheory.TranslationQuiverComponentGraph
import MagnitudeConjecture.CategoryTheory.TranslationQuiverDeckAction
import MagnitudeConjecture.CategoryTheory.TranslationQuiverStable

/-!
# Periodic stable components as translation quivers

The component graph records a periodic stable component as a quotient of
periodic translation orbits.  This file exposes the actual vertices and
arrows belonging to one such component and equips them with the induced
stable polarized right-translation-quiver structure.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.MeshCategory.RightMeshData.IsTauInjective

universe u

variable {Q : Type u} [Quiver.{u} Q]
variable (T : RightMeshData Q) (hT : T.IsTauInjective)

/-- A vertex belongs to a fixed periodic component when it is periodic and
its intrinsic translation orbit represents that component. -/
def IsInPeriodicComponent
    (E : PeriodicComponent T hT) (x : Q) : Prop :=
  ∃ hx : IsPeriodicVertex T x,
    periodicComponentClass T hT
        (show PeriodicTauOrbit T from ⟨tauClass T x, hx⟩) = E

/-- The actual vertices of one periodic stable component. -/
abbrev PeriodicComponentVertex (E : PeriodicComponent T hT) :=
  {x : Q // IsInPeriodicComponent T hT E x}

theorem periodicComponentVertex_isPeriodic
    {E : PeriodicComponent T hT} (x : PeriodicComponentVertex T hT E) :
    IsPeriodicVertex T x.1 :=
  x.2.choose

theorem periodicComponentVertex_component
    {E : PeriodicComponent T hT} (x : PeriodicComponentVertex T hT E) :
    periodicComponentClass T hT
        (show PeriodicTauOrbit T from
          ⟨tauClass T x.1, periodicComponentVertex_isPeriodic T hT x⟩) = E :=
  x.2.choose_spec

/-- Every actual vertex of a periodic component collapses to that component's
distinguished component-graph vertex. -/
theorem componentGraphVertexOf_periodicComponentVertex
    {E : PeriodicComponent T hT} (x : PeriodicComponentVertex T hT E) :
    componentGraphVertexOf T hT x.1 = Sum.inr E := by
  rw [componentGraphVertexOf,
    collapseTauOrbit_of_periodic T hT _
      ((isPeriodicTauOrbit_tauClass T x.1).2
        (periodicComponentVertex_isPeriodic T hT x))]
  exact congrArg Sum.inr (periodicComponentVertex_component T hT x)

/-- A vertex in a periodic component is not projective. -/
theorem periodicComponentVertex_not_projective
    {E : PeriodicComponent T hT} (x : PeriodicComponentVertex T hT E) :
    x.1 ∉ T.projective :=
  periodicComponentVertex_isPeriodic T hT x x.1
    ((tauOrbitSetoid T).refl x.1)

/-- Translation preserves the chosen periodic component. -/
def periodicComponentTau
    {E : PeriodicComponent T hT} (x : PeriodicComponentVertex T hT E) :
    PeriodicComponentVertex T hT E := by
  let sx : {x : Q // x ∉ T.projective} :=
    ⟨x.1, periodicComponentVertex_not_projective T hT x⟩
  have hrelated : (tauOrbitSetoid T) x.1 (T.tau sx) :=
    tau_related T sx
  have hperiodic : IsPeriodicVertex T (T.tau sx) :=
    isPeriodicVertex_of_related T
      (periodicComponentVertex_isPeriodic T hT x) hrelated
  refine ⟨T.tau sx, hperiodic, ?_⟩
  have horbit :
      (show PeriodicTauOrbit T from ⟨tauClass T (T.tau sx), hperiodic⟩) =
        (show PeriodicTauOrbit T from
          ⟨tauClass T x.1, periodicComponentVertex_isPeriodic T hT x⟩) := by
    apply Subtype.ext
    exact Quotient.sound ((tauOrbitSetoid T).symm hrelated)
  rw [horbit]
  exact periodicComponentVertex_component T hT x

instance periodicComponentQuiver
    (E : PeriodicComponent T hT) :
    Quiver (PeriodicComponentVertex T hT E) where
  Hom x y := x.1 ⟶ y.1

/-- The sigma-orbit of an arrow internal to a periodic component is
periodic. -/
theorem periodicComponent_arrowOrbit_isPeriodic
    {E : PeriodicComponent T hT}
    {x y : PeriodicComponentVertex T hT E} (a : x ⟶ y) :
    IsPeriodicArrowOrbit T hT (arrowOrbitClass T hT a) := by
  let e := arrowOrbitClass T hT a
  have hends := Sym2.eq_iff.mp
    (arrowOrbitEnds_eq_mk_source_target T hT e)
  have hx : IsPeriodicTauOrbit T (tauClass T x.1) :=
    (isPeriodicTauOrbit_tauClass T x.1).2
      (periodicComponentVertex_isPeriodic T hT x)
  have hy : IsPeriodicTauOrbit T (tauClass T y.1) :=
    (isPeriodicTauOrbit_tauClass T y.1).2
      (periodicComponentVertex_isPeriodic T hT y)
  rcases hends with hends | hends
  · exact ⟨hends.1 ▸ hx, hends.2 ▸ hy⟩
  · exact ⟨hends.2 ▸ hy, hends.1 ▸ hx⟩

/-- Every internal arrow of a periodic component gives that component's one
distinguished loop in the component graph. -/
theorem componentGraphEdgeOf_periodicComponentArrow
    {E : PeriodicComponent T hT}
    {x y : PeriodicComponentVertex T hT E} (a : x ⟶ y) :
    componentGraphEdgeOfArrowOrbit T hT (arrowOrbitClass T hT a) =
      Sum.inr E := by
  let e := arrowOrbitClass T hT a
  let he := periodicComponent_arrowOrbit_isPeriodic T hT a
  rw [componentGraphEdgeOfArrowOrbit_of_periodic T hT e he]
  congr 1
  have hends := Sym2.eq_iff.mp
    (arrowOrbitEnds_eq_mk_source_target T hT e)
  rcases hends with hends | hends
  · have hs :
        (show PeriodicTauOrbit T from
            ⟨arrowOrbitSource T hT e, he.1⟩) =
          ⟨tauClass T x.1,
            (isPeriodicTauOrbit_tauClass T x.1).2
              (periodicComponentVertex_isPeriodic T hT x)⟩ := by
      exact Subtype.ext hends.1.symm
    rw [hs]
    exact periodicComponentVertex_component T hT x
  · have hs :
        (show PeriodicTauOrbit T from
            ⟨arrowOrbitSource T hT e, he.1⟩) =
          ⟨tauClass T y.1,
            (isPeriodicTauOrbit_tauClass T y.1).2
              (periodicComponentVertex_isPeriodic T hT y)⟩ := by
      exact Subtype.ext hends.2.symm
    rw [hs]
    exact periodicComponentVertex_component T hT y

/-- Forgetting the component witness includes the periodic component into the
ambient quiver. -/
def periodicComponentInclusion
    (E : PeriodicComponent T hT) :
    PeriodicComponentVertex T hT E ⥤q Q where
  obj := Subtype.val
  map := id

@[simp]
theorem periodicComponentInclusion_obj
    (E : PeriodicComponent T hT) (x : PeriodicComponentVertex T hT E) :
    (periodicComponentInclusion T hT E).obj x = x.1 :=
  rfl

@[simp]
theorem periodicComponentInclusion_map
    {E : PeriodicComponent T hT}
    {x y : PeriodicComponentVertex T hT E} (a : x ⟶ y) :
    (periodicComponentInclusion T hT E).map a = a :=
  rfl

/-- Every quotient component has an actual vertex representative. -/
theorem periodicComponentVertex_nonempty
    (E : PeriodicComponent T hT) :
    Nonempty (PeriodicComponentVertex T hT E) := by
  let X : PeriodicTauOrbit T := Quotient.out E
  let x : Q := Quotient.out X.1
  have hxClass : tauClass T x = X.1 := Quotient.out_eq X.1
  have hxPeriodic : IsPeriodicVertex T x := by
    rw [← isPeriodicTauOrbit_tauClass T x, hxClass]
    exact X.2
  refine ⟨⟨x, hxPeriodic, ?_⟩⟩
  have hX :
      (show PeriodicTauOrbit T from ⟨tauClass T x, hxPeriodic⟩) = X := by
    apply Subtype.ext
    exact hxClass
  rw [hX]
  exact Quotient.out_eq E

/-- The induced polarized right-mesh data on one periodic component.  Its
projective boundary is empty by construction. -/
def periodicComponentRightMeshData
    (E : PeriodicComponent T hT) :
    RightMeshData (PeriodicComponentVertex T hT E) where
  projective := ∅
  tau := fun x ↦ periodicComponentTau T hT x.1
  arrowEquiv := by
    intro x y
    exact T.arrowEquiv
      ⟨x.1.1, periodicComponentVertex_not_projective T hT x.1⟩ y.1

@[simp]
theorem periodicComponentRightMeshData_projective
    (E : PeriodicComponent T hT) :
    (periodicComponentRightMeshData T hT E).projective = ∅ :=
  rfl

@[simp]
theorem periodicComponentRightMeshData_tau_val
    {E : PeriodicComponent T hT}
    (x : {x : PeriodicComponentVertex T hT E //
      x ∉ (periodicComponentRightMeshData T hT E).projective}) :
    ((periodicComponentRightMeshData T hT E).tau x).1 =
      T.tau
        ⟨x.1.1, periodicComponentVertex_not_projective T hT x.1⟩ :=
  rfl

/-- The total stable translation on a periodic component is injective. -/
theorem periodicComponent_stableTau_injective
    (E : PeriodicComponent T hT) :
    Function.Injective
      ((periodicComponentRightMeshData T hT E).stableTau
        (periodicComponentRightMeshData_projective T hT E)) := by
  intro x y hxy
  apply Subtype.ext
  have htau :
      T.tau ⟨x.1, periodicComponentVertex_not_projective T hT x⟩ =
        T.tau ⟨y.1, periodicComponentVertex_not_projective T hT y⟩ :=
    congrArg Subtype.val hxy
  exact congrArg
    (fun z : {q : Q // q ∉ T.projective} ↦ z.1) (hT htau)

/-- Finiteness promotes the injective component translation to a
permutation. -/
theorem periodicComponent_stableTau_bijective [Finite Q]
    (E : PeriodicComponent T hT) :
    Function.Bijective
      ((periodicComponentRightMeshData T hT E).stableTau
        (periodicComponentRightMeshData_projective T hT E)) := by
  let hinjective := periodicComponent_stableTau_injective T hT E
  exact ⟨hinjective, Finite.surjective_of_injective hinjective⟩

/-- Membership in a periodic component is constant along an intrinsic
tau-orbit. -/
theorem isInPeriodicComponent_of_tau_related
    {E : PeriodicComponent T hT} {x y : Q}
    (hx : IsInPeriodicComponent T hT E x)
    (hxy : (tauOrbitSetoid T) x y) :
    IsInPeriodicComponent T hT E y := by
  let hxperiodic := hx.choose
  let hyperiodic := isPeriodicVertex_of_related T hxperiodic hxy
  refine ⟨hyperiodic, ?_⟩
  have horbit :
      (show PeriodicTauOrbit T from ⟨tauClass T y, hyperiodic⟩) =
        (show PeriodicTauOrbit T from ⟨tauClass T x, hxperiodic⟩) := by
    apply Subtype.ext
    exact (Quotient.sound hxy).symm
  rw [horbit]
  exact hx.choose_spec

/-- Two component vertices in the same ambient tau-orbit are joined by an
augmented walk using the formal mesh edges of the induced stable component. -/
theorem nonempty_periodicComponentWalk_of_tau_related
    {E : PeriodicComponent T hT}
    (x y : PeriodicComponentVertex T hT E)
    (hxy : (tauOrbitSetoid T) x.1 y.1) :
    Nonempty
      (UniversalCover.Walk (periodicComponentRightMeshData T hT E) x y) := by
  let D := periodicComponentRightMeshData T hT E
  let hstable := periodicComponentRightMeshData_projective T hT E
  have hwalk : ∀ {a b : Q}, (tauOrbitSetoid T) a b →
      ∀ (ha : IsInPeriodicComponent T hT E a)
        (hb : IsInPeriodicComponent T hT E b),
        Nonempty (UniversalCover.Walk D ⟨a, ha⟩ ⟨b, hb⟩) := by
    intro a b hab
    induction hab with
    | rel a b hab =>
        intro ha hb
        rcases hab with ⟨s, hs, ht⟩
        let xa : PeriodicComponentVertex T hT E := ⟨a, ha⟩
        let yb : PeriodicComponentVertex T hT E := ⟨b, hb⟩
        let sx : {z : PeriodicComponentVertex T hT E // z ∉ D.projective} :=
          D.stableNonprojective hstable xa
        have hsource :
            (⟨a, periodicComponentVertex_not_projective T hT xa⟩ :
              {z : Q // z ∉ T.projective}) = s := by
          apply Subtype.ext
          exact hs.symm
        have htarget : D.tau sx = yb := by
          apply Subtype.ext
          change T.tau
              ⟨a, periodicComponentVertex_not_projective T hT xa⟩ = b
          rw [hsource]
          exact ht
        exact ⟨(UniversalCover.meshArrowPath D sx).cast rfl htarget⟩
    | refl a =>
        intro ha hb
        have hvertices :
            (⟨a, ha⟩ : PeriodicComponentVertex T hT E) = ⟨a, hb⟩ :=
          Subtype.ext rfl
        exact ⟨(Quiver.Path.nil).cast rfl hvertices⟩
    | symm a b hab ih =>
        intro ha hb
        exact ⟨(ih hb ha).some.reverse⟩
    | trans a b c hab hbc ih₁ ih₂ =>
        intro ha hc
        let hb := isInPeriodicComponent_of_tau_related T hT ha hab
        exact ⟨(ih₁ ha hb).some.comp (ih₂ hb hc).some⟩
  exact hwalk hxy x.2 y.2

/-- A generating sigma-adjacency between two periodic tau-orbits gives an
augmented walk between arbitrary vertices representing those orbits. -/
theorem nonempty_periodicComponentWalk_of_periodicAdjacent
    {E : PeriodicComponent T hT}
    (x y : PeriodicComponentVertex T hT E)
    (hxy : PeriodicAdjacent T hT
      (show PeriodicTauOrbit T from
        ⟨tauClass T x.1, periodicComponentVertex_isPeriodic T hT x⟩)
      (show PeriodicTauOrbit T from
        ⟨tauClass T y.1, periodicComponentVertex_isPeriodic T hT y⟩)) :
    Nonempty
      (UniversalCover.Walk (periodicComponentRightMeshData T hT E) x y) := by
  let D := periodicComponentRightMeshData T hT E
  have horiented : ∀ (x y : PeriodicComponentVertex T hT E)
      (e : ArrowOrbit T hT),
      arrowOrbitSource T hT e = tauClass T x.1 ∧
        arrowOrbitTarget T hT e = tauClass T y.1 →
      Nonempty (UniversalCover.Walk D x y) := by
    intro x y e he
    rcases hsource : Quotient.out e with ⟨u, va⟩
    rcases htarget : va with ⟨v, a⟩
    have houtTarget : (Quotient.out e).2.1 = v := by
      rw [hsource]
      exact congrArg Sigma.fst htarget
    have huClass : tauClass T u = tauClass T x.1 := by
      simpa only [arrowOrbitSource, arrowOrbitRepresentative, hsource] using he.1
    have hvClass : tauClass T v = tauClass T y.1 := by
      simpa only [arrowOrbitTarget, arrowOrbitRepresentative, houtTarget] using he.2
    have hxu : (tauOrbitSetoid T) x.1 u :=
      Quotient.exact huClass.symm
    have hyv : (tauOrbitSetoid T) y.1 v :=
      Quotient.exact hvClass.symm
    let hu := isInPeriodicComponent_of_tau_related T hT x.2 hxu
    let hv := isInPeriodicComponent_of_tau_related T hT y.2 hyv
    let xu : PeriodicComponentVertex T hT E := ⟨u, hu⟩
    let yv : PeriodicComponentVertex T hT E := ⟨v, hv⟩
    let px :=
      (nonempty_periodicComponentWalk_of_tau_related T hT x xu hxu).some
    let py :=
      (nonempty_periodicComponentWalk_of_tau_related T hT y yv hyv).some
    let pa : UniversalCover.Walk D xu yv :=
      UniversalCover.oldArrowPath D a
    exact ⟨(px.comp pa).comp py.reverse⟩
  rcases hxy with ⟨e, he | he⟩
  · exact horiented x y e he
  · exact ⟨(horiented y x e he).some.reverse⟩

/-- Every induced periodic component is connected by augmented walks from
any chosen base vertex. -/
theorem periodicComponent_isWalkConnectedAt
    (E : PeriodicComponent T hT)
    (x₀ : PeriodicComponentVertex T hT E) :
    UniversalCover.IsWalkConnectedAt
      (periodicComponentRightMeshData T hT E) x₀ := by
  let D := periodicComponentRightMeshData T hT E
  intro y
  let X₀ : PeriodicTauOrbit T :=
    ⟨tauClass T x₀.1, periodicComponentVertex_isPeriodic T hT x₀⟩
  let Y : PeriodicTauOrbit T :=
    ⟨tauClass T y.1, periodicComponentVertex_isPeriodic T hT y⟩
  have hclasses : periodicComponentClass T hT X₀ =
      periodicComponentClass T hT Y :=
    (periodicComponentVertex_component T hT x₀).trans
      (periodicComponentVertex_component T hT y).symm
  have hrelated : (periodicComponentSetoid T hT) X₀ Y :=
    Quotient.exact hclasses
  have hwalk : ∀ {X Y : PeriodicTauOrbit T},
      (periodicComponentSetoid T hT) X Y →
      ∀ (x y : PeriodicComponentVertex T hT E),
        tauClass T x.1 = X.1 → tauClass T y.1 = Y.1 →
        Nonempty (UniversalCover.Walk D x y) := by
    intro X Y hXY
    induction hXY with
    | rel X Y hXY =>
        intro x y hx hy
        have hX :
            (show PeriodicTauOrbit T from
              ⟨tauClass T x.1,
                periodicComponentVertex_isPeriodic T hT x⟩) = X :=
          Subtype.ext hx
        have hY :
            (show PeriodicTauOrbit T from
              ⟨tauClass T y.1,
                periodicComponentVertex_isPeriodic T hT y⟩) = Y :=
          Subtype.ext hy
        rw [← hX, ← hY] at hXY
        exact nonempty_periodicComponentWalk_of_periodicAdjacent
          T hT x y hXY
    | refl X =>
        intro x y hx hy
        exact nonempty_periodicComponentWalk_of_tau_related T hT x y
          (Quotient.exact (hx.trans hy.symm))
    | symm X Y hXY ih =>
        intro x y hx hy
        exact ⟨(ih y x hy hx).some.reverse⟩
    | trans X Y Z hXY hYZ ih₁ ih₂ =>
        intro x z hx hz
        have hX :
            (show PeriodicTauOrbit T from
              ⟨tauClass T x.1,
                periodicComponentVertex_isPeriodic T hT x⟩) = X :=
          Subtype.ext hx
        have hXE : periodicComponentClass T hT X = E := by
          rw [← hX]
          exact periodicComponentVertex_component T hT x
        have hYE : periodicComponentClass T hT Y = E :=
          (Quotient.sound hXY).symm.trans hXE
        let u : Q := Quotient.out Y.1
        have huClass : tauClass T u = Y.1 := Quotient.out_eq Y.1
        have huPeriodic : IsPeriodicVertex T u := by
          rw [← isPeriodicTauOrbit_tauClass T u, huClass]
          exact Y.2
        have huComponent :
            periodicComponentClass T hT
                (show PeriodicTauOrbit T from
                  ⟨tauClass T u, huPeriodic⟩) = E := by
          have huOrbit :
              (show PeriodicTauOrbit T from
                ⟨tauClass T u, huPeriodic⟩) = Y :=
            Subtype.ext huClass
          rw [huOrbit]
          exact hYE
        let yu : PeriodicComponentVertex T hT E :=
          ⟨u, huPeriodic, huComponent⟩
        exact ⟨(ih₁ x yu hx huClass).some.comp
          (ih₂ yu z huClass hz).some⟩
  exact hwalk hrelated x₀ y rfl rfl

/-- Mesh arrows in the induced component are exactly ambient mesh arrows
whose middle vertex lies in that component. -/
def periodicComponentMeshArrowEquiv
    (E : PeriodicComponent T hT)
    (x : {x : PeriodicComponentVertex T hT E //
      x ∉ (periodicComponentRightMeshData T hT E).projective}) :
    (periodicComponentRightMeshData T hT E).MeshArrow x ≃
      {a : T.MeshArrow
          ⟨x.1.1, periodicComponentVertex_not_projective T hT x.1⟩ //
        IsInPeriodicComponent T hT E a.1} where
  toFun a := ⟨⟨a.1.1, a.2⟩, a.1.2⟩
  invFun a := ⟨⟨a.1.1, a.2⟩, a.1.2⟩
  left_inv a := by
    rcases a with ⟨y, a⟩
    rfl
  right_inv a := by
    rcases a with ⟨⟨y, a⟩, hy⟩
    rfl

@[simp]
theorem periodicComponentMeshArrowEquiv_apply
    (E : PeriodicComponent T hT)
    (x : {x : PeriodicComponentVertex T hT E //
      x ∉ (periodicComponentRightMeshData T hT E).projective})
    (a : (periodicComponentRightMeshData T hT E).MeshArrow x) :
    (periodicComponentMeshArrowEquiv T hT E x a).1 =
      (show T.MeshArrow
          ⟨x.1.1, periodicComponentVertex_not_projective T hT x.1⟩ from
        ⟨a.1.1, a.2⟩) :=
  rfl

/-- Forgetting component witnesses sends a component mesh path to the
corresponding ambient mesh path. -/
theorem periodicComponentInclusion_mapPath_meshPath
    (E : PeriodicComponent T hT)
    (x : {x : PeriodicComponentVertex T hT E //
      x ∉ (periodicComponentRightMeshData T hT E).projective})
    (a : (periodicComponentRightMeshData T hT E).MeshArrow x) :
    (periodicComponentInclusion T hT E).mapPath
        ((periodicComponentRightMeshData T hT E).meshPath x a) =
      T.meshPath
        ⟨x.1.1, periodicComponentVertex_not_projective T hT x.1⟩
        (periodicComponentMeshArrowEquiv T hT E x a).1 :=
  rfl

end MagnitudeConjecture.MeshCategory.RightMeshData.IsTauInjective
