import MagnitudeConjecture.CategoryTheory.TranslationQuiverNonperiodicOrbit

/-!
# The Bongartz--Gabriel component graph

Periodic tau-cycles are grouped into connected components of the stable part.
The resulting graph has one vertex and one distinguished loop for each such
component, while its remaining vertices and edges are the nonperiodic tau- and
sigma-orbits.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.MeshCategory.RightMeshData.IsTauInjective

universe u

variable {Q : Type u} [Quiver.{u} Q]
variable (T : RightMeshData Q) (hT : T.IsTauInjective)

/-- A sigma-orbit is periodic when both of its endpoint tau-orbits are
periodic.  These are precisely the edges retained inside the stable periodic
part before each connected component is contracted. -/
def IsPeriodicArrowOrbit (e : ArrowOrbit T hT) : Prop :=
  IsPeriodicTauOrbit T (arrowOrbitSource T hT e) ∧
    IsPeriodicTauOrbit T (arrowOrbitTarget T hT e)

/-- Sigma-orbits internal to the periodic stable part. -/
abbrev PeriodicArrowOrbit :=
  {e : ArrowOrbit T hT // IsPeriodicArrowOrbit T hT e}

/-- The sigma-orbits which survive as ordinary edges after contraction of the
periodic stable components. -/
abbrev NonperiodicArrowOrbit :=
  {e : ArrowOrbit T hT // ¬ IsPeriodicArrowOrbit T hT e}

/-- The canonical projective-source representative of a nonperiodic
sigma-orbit. -/
noncomputable def nonperiodicArrowBoundaryRepresentative [Finite Q]
    (e : NonperiodicArrowOrbit T hT) : Arrow T :=
  (sigmaBoundaryNormalForm T hT
    ⟨arrowOrbitRepresentative T hT e.1,
      arrowOrbitRepresentative_endpoint_nonperiodic T hT e.1 e.2⟩).boundary.1

theorem nonperiodicArrowBoundaryRepresentative_source_projective [Finite Q]
    (e : NonperiodicArrowOrbit T hT) :
    (nonperiodicArrowBoundaryRepresentative T hT e).1 ∈ T.projective :=
  (sigmaBoundaryNormalForm T hT
    ⟨arrowOrbitRepresentative T hT e.1,
      arrowOrbitRepresentative_endpoint_nonperiodic T hT e.1 e.2⟩).source_projective

theorem nonperiodicArrowBoundaryRepresentative_class [Finite Q]
    (e : NonperiodicArrowOrbit T hT) :
    Quotient.mk (arrowOrbitSetoid T hT)
        (nonperiodicArrowBoundaryRepresentative T hT e) = e.1 :=
  (sigmaBoundaryNormalForm T hT
    ⟨arrowOrbitRepresentative T hT e.1,
      arrowOrbitRepresentative_endpoint_nonperiodic T hT e.1 e.2⟩).orbit_eq.trans
    (Quotient.out_eq e.1)

/-- Undirected adjacency of two periodic tau-cycles through a periodic
sigma-orbit. -/
def PeriodicAdjacent (X Y : PeriodicTauOrbit T) : Prop :=
  ∃ e : ArrowOrbit T hT,
    (arrowOrbitSource T hT e = X.1 ∧
        arrowOrbitTarget T hT e = Y.1) ∨
      (arrowOrbitSource T hT e = Y.1 ∧
        arrowOrbitTarget T hT e = X.1)

theorem periodicAdjacent_symm {X Y : PeriodicTauOrbit T}
    (hXY : PeriodicAdjacent T hT X Y) :
    PeriodicAdjacent T hT Y X := by
  rcases hXY with ⟨e, h | h⟩
  · exact ⟨e, Or.inr h⟩
  · exact ⟨e, Or.inl h⟩

/-- Connectedness in the periodic stable part. -/
def periodicComponentSetoid : Setoid (PeriodicTauOrbit T) :=
  Relation.EqvGen.setoid (PeriodicAdjacent T hT)

/-- Periodic stable components of the finite translation quiver. -/
def PeriodicComponent := Quotient (periodicComponentSetoid T hT)

/-- The periodic stable component containing a periodic tau-cycle. -/
def periodicComponentClass (X : PeriodicTauOrbit T) :
    PeriodicComponent T hT :=
  Quotient.mk _ X

/-- Adjoining one periodic sigma-orbit does not change the periodic stable
component. -/
theorem periodicAdjacent_related {X Y : PeriodicTauOrbit T}
    (hXY : PeriodicAdjacent T hT X Y) :
    periodicComponentClass T hT X = periodicComponentClass T hT Y :=
  Quotient.sound (Relation.EqvGen.rel _ _ hXY)

/-- Vertices of the Bongartz--Gabriel component graph: nonperiodic tau-orbits
and periodic stable components. -/
abbrev ComponentGraphVertex :=
  NonperiodicTauOrbit T ⊕ PeriodicComponent T hT

/-- Collapse a tau-orbit to the corresponding component-graph vertex. -/
noncomputable def collapseTauOrbit (o : TauOrbit T) :
    ComponentGraphVertex T hT := by
  classical
  exact if ho : IsPeriodicTauOrbit T o then
    Sum.inr (periodicComponentClass T hT ⟨o, ho⟩)
  else Sum.inl ⟨o, ho⟩

@[simp]
theorem collapseTauOrbit_of_nonperiodic (o : TauOrbit T)
    (ho : ¬ IsPeriodicTauOrbit T o) :
    collapseTauOrbit T hT o = Sum.inl ⟨o, ho⟩ := by
  simp [collapseTauOrbit, ho]

@[simp]
theorem collapseTauOrbit_of_periodic (o : TauOrbit T)
    (ho : IsPeriodicTauOrbit T o) :
    collapseTauOrbit T hT o =
      Sum.inr (periodicComponentClass T hT ⟨o, ho⟩) := by
  simp [collapseTauOrbit, ho]

/-- Both endpoints of a periodic sigma-orbit collapse to the same periodic
stable component. -/
theorem collapseTauOrbit_source_eq_target_of_periodic
    (e : ArrowOrbit T hT) (he : IsPeriodicArrowOrbit T hT e) :
    collapseTauOrbit T hT (arrowOrbitSource T hT e) =
      collapseTauOrbit T hT (arrowOrbitTarget T hT e) := by
  let X : PeriodicTauOrbit T := ⟨arrowOrbitSource T hT e, he.1⟩
  let Y : PeriodicTauOrbit T := ⟨arrowOrbitTarget T hT e, he.2⟩
  have hXY : PeriodicAdjacent T hT X Y :=
    ⟨e, Or.inl ⟨rfl, rfl⟩⟩
  rw [collapseTauOrbit_of_periodic T hT _ he.1,
    collapseTauOrbit_of_periodic T hT _ he.2]
  exact congrArg Sum.inr (periodicAdjacent_related T hT hXY)

/-- Edges of the component graph before exposing endpoints: one ordinary edge
for each nonperiodic sigma-orbit and one distinguished loop for each periodic
stable component. -/
abbrev ComponentGraphEdge :=
  NonperiodicArrowOrbit T hT ⊕ PeriodicComponent T hT

/-- Chosen source of a component-graph edge. -/
def componentGraphEdgeSource : ComponentGraphEdge T hT →
    ComponentGraphVertex T hT
  | Sum.inl e => collapseTauOrbit T hT (arrowOrbitSource T hT e.1)
  | Sum.inr E => Sum.inr E

/-- Chosen target of a component-graph edge. -/
def componentGraphEdgeTarget : ComponentGraphEdge T hT →
    ComponentGraphVertex T hT
  | Sum.inl e => collapseTauOrbit T hT (arrowOrbitTarget T hT e.1)
  | Sum.inr E => Sum.inr E

/-- The endpoint-indexed edge type of the component graph. -/
def ComponentGraphArrow (X Y : ComponentGraphVertex T hT) :=
  {e : ComponentGraphEdge T hT //
    componentGraphEdgeSource T hT e = X ∧
      componentGraphEdgeTarget T hT e = Y}

instance componentGraphQuiver : Quiver (ComponentGraphVertex T hT) where
  Hom := ComponentGraphArrow T hT

/-- Every nonperiodic sigma-orbit supplies its chosen oriented edge. -/
def nonperiodicArrowOrbitEdge (e : NonperiodicArrowOrbit T hT) :
    @Quiver.Hom (ComponentGraphVertex T hT) (componentGraphQuiver T hT)
      (collapseTauOrbit T hT (arrowOrbitSource T hT e.1))
      (collapseTauOrbit T hT (arrowOrbitTarget T hT e.1)) :=
  ⟨Sum.inl e, rfl, rfl⟩

/-- Every periodic stable component contributes one distinguished loop. -/
def periodicComponentLoop (E : PeriodicComponent T hT) :
    @Quiver.Hom (ComponentGraphVertex T hT) (componentGraphQuiver T hT)
      (Sum.inr E) (Sum.inr E) :=
  ⟨Sum.inr E, rfl, rfl⟩

/-- The component-graph vertex containing an original translation-quiver
vertex. -/
def componentGraphVertexOf (x : Q) : ComponentGraphVertex T hT :=
  collapseTauOrbit T hT (tauClass T x)

/-- Translation does not change the collapsed component-graph vertex. -/
theorem componentGraphVertexOf_tau
    (x : {x : Q // x ∉ T.projective}) :
    componentGraphVertexOf T hT (T.tau x) =
      componentGraphVertexOf T hT x.1 := by
  exact congrArg (collapseTauOrbit T hT)
    (Quotient.sound (tau_related T x)).symm

/-- Any unindexed component-graph edge, exposed with its chosen endpoints. -/
def componentGraphArrowOfEdge (e : ComponentGraphEdge T hT) :
    @Quiver.Hom (ComponentGraphVertex T hT) (componentGraphQuiver T hT)
      (componentGraphEdgeSource T hT e)
      (componentGraphEdgeTarget T hT e) :=
  ⟨e, rfl, rfl⟩

/-- A sigma-orbit gives its surviving component-graph edge.  Periodic
sigma-orbits all give the distinguished loop of their periodic component. -/
noncomputable def componentGraphEdgeOfArrowOrbit
    (e : ArrowOrbit T hT) : ComponentGraphEdge T hT := by
  classical
  exact if he : IsPeriodicArrowOrbit T hT e then
    Sum.inr (periodicComponentClass T hT
      (show PeriodicTauOrbit T from
        ⟨arrowOrbitSource T hT e, he.1⟩))
  else Sum.inl ⟨e, he⟩

@[simp]
theorem componentGraphEdgeOfArrowOrbit_of_periodic
    (e : ArrowOrbit T hT) (he : IsPeriodicArrowOrbit T hT e) :
    componentGraphEdgeOfArrowOrbit T hT e =
      Sum.inr (periodicComponentClass T hT
        (show PeriodicTauOrbit T from
          ⟨arrowOrbitSource T hT e, he.1⟩)) := by
  simp [componentGraphEdgeOfArrowOrbit, he]

@[simp]
theorem componentGraphEdgeOfArrowOrbit_of_nonperiodic
    (e : ArrowOrbit T hT) (he : ¬ IsPeriodicArrowOrbit T hT e) :
    componentGraphEdgeOfArrowOrbit T hT e = Sum.inl ⟨e, he⟩ := by
  simp [componentGraphEdgeOfArrowOrbit, he]

/-- The chosen source of the edge associated with a sigma-orbit is the
collapsed source tau-orbit. -/
theorem componentGraphEdgeOfArrowOrbit_source
    (e : ArrowOrbit T hT) :
    componentGraphEdgeSource T hT
        (componentGraphEdgeOfArrowOrbit T hT e) =
      collapseTauOrbit T hT (arrowOrbitSource T hT e) := by
  classical
  by_cases he : IsPeriodicArrowOrbit T hT e
  · rw [componentGraphEdgeOfArrowOrbit, dif_pos he]
    exact (collapseTauOrbit_of_periodic T hT _ he.1).symm
  · rw [componentGraphEdgeOfArrowOrbit, dif_neg he]
    rfl

/-- The chosen target of the edge associated with a sigma-orbit is the
collapsed target tau-orbit. -/
theorem componentGraphEdgeOfArrowOrbit_target
    (e : ArrowOrbit T hT) :
    componentGraphEdgeTarget T hT
        (componentGraphEdgeOfArrowOrbit T hT e) =
      collapseTauOrbit T hT (arrowOrbitTarget T hT e) := by
  classical
  by_cases he : IsPeriodicArrowOrbit T hT e
  · rw [componentGraphEdgeOfArrowOrbit, dif_pos he]
    change Sum.inr (periodicComponentClass T hT
        (show PeriodicTauOrbit T from
          ⟨arrowOrbitSource T hT e, he.1⟩)) =
      collapseTauOrbit T hT (arrowOrbitTarget T hT e)
    rw [← collapseTauOrbit_source_eq_target_of_periodic T hT e he]
    exact (collapseTauOrbit_of_periodic T hT _ he.1).symm
  · rw [componentGraphEdgeOfArrowOrbit, dif_neg he]
    rfl

/-- A concrete ordinary arrow regarded as its sigma-orbit. -/
def arrowOrbitClass {x y : Q} (a : x ⟶ y) : ArrowOrbit T hT :=
  Quotient.mk _ ⟨x, y, a⟩

/-- The unordered collapsed endpoints of an ordinary arrow agree with the
chosen endpoints of its component-graph edge. -/
theorem componentGraphEdgeOfArrowOrbit_incidence
    {x y : Q} (a : x ⟶ y) :
    s(componentGraphVertexOf T hT x, componentGraphVertexOf T hT y) =
      s(componentGraphEdgeSource T hT
          (componentGraphEdgeOfArrowOrbit T hT (arrowOrbitClass T hT a)),
        componentGraphEdgeTarget T hT
          (componentGraphEdgeOfArrowOrbit T hT
            (arrowOrbitClass T hT a))) := by
  let e := arrowOrbitClass T hT a
  have hends := arrowOrbitEnds_eq_mk_source_target T hT e
  have hcollapsed := congrArg
    (Sym2.map (collapseTauOrbit T hT)) hends
  calc
    s(componentGraphVertexOf T hT x, componentGraphVertexOf T hT y) =
        s(collapseTauOrbit T hT (arrowOrbitSource T hT e),
          collapseTauOrbit T hT (arrowOrbitTarget T hT e)) := by
      simpa only [e, arrowOrbitClass, componentGraphVertexOf,
        arrowOrbitEnds_mk, arrowEnds, Sym2.map_mk] using hcollapsed
    _ = _ := by
      rw [componentGraphEdgeOfArrowOrbit_source,
        componentGraphEdgeOfArrowOrbit_target]

/-- Equivalently, an ordinary arrow meets its surviving component-graph edge
in the chosen orientation or in the reverse orientation. -/
theorem componentGraphEdgeOfArrowOrbit_incidence_cases
    {x y : Q} (a : x ⟶ y) :
    let e := componentGraphEdgeOfArrowOrbit T hT (arrowOrbitClass T hT a)
    (componentGraphVertexOf T hT x = componentGraphEdgeSource T hT e ∧
        componentGraphVertexOf T hT y = componentGraphEdgeTarget T hT e) ∨
      (componentGraphVertexOf T hT x = componentGraphEdgeTarget T hT e ∧
        componentGraphVertexOf T hT y = componentGraphEdgeSource T hT e) := by
  exact Sym2.eq_iff.mp
    (componentGraphEdgeOfArrowOrbit_incidence T hT a)

end MagnitudeConjecture.MeshCategory.RightMeshData.IsTauInjective
