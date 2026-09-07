import MagnitudeConjecture.CategoryTheory.TranslationQuiverDeckAction

/-!
# Walk components of a polarized translation quiver

The universal-cover construction uses walks in the symmetrified quiver
obtained by adjoining one formal edge from every nonprojective vertex to its
translate.  Their reachability relation gives the component notion relevant
to that construction.  Ordinary arrows and translation edges both remain in
one such component.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover

universe u v w

variable {Q : Type v} [Quiver.{w} Q]

/-- Two vertices are walk-connected when an augmented walk joins them. -/
def WalkConnected (T : RightMeshData Q) (x y : Q) : Prop :=
  Nonempty (Walk T x y)

/-- Augmented walk-connectivity is reflexive. -/
theorem walkConnected_refl (T : RightMeshData Q) (x : Q) :
    WalkConnected T x x :=
  ⟨Quiver.Path.nil⟩

/-- Augmented walk-connectivity is symmetric. -/
theorem walkConnected_symm (T : RightMeshData Q) {x y : Q} :
    WalkConnected T x y → WalkConnected T y x :=
  Nonempty.map (reverseWalk T)

/-- Augmented walk-connectivity is transitive. -/
theorem walkConnected_trans (T : RightMeshData Q) {x y z : Q} :
    WalkConnected T x y → WalkConnected T y z → WalkConnected T x z :=
  Nonempty.map2 Quiver.Path.comp

/-- The equivalence relation of augmented walk-connectivity. -/
def walkComponentSetoid (T : RightMeshData Q) : Setoid Q where
  r := WalkConnected T
  iseqv := {
    refl := walkConnected_refl T
    symm := walkConnected_symm T
    trans := walkConnected_trans T }

/-- Components of the symmetrified augmented translation quiver. -/
abbrev WalkComponent (T : RightMeshData Q) :=
  Quotient (walkComponentSetoid T)

/-- The augmented-walk component containing a vertex. -/
def walkComponentClass (T : RightMeshData Q) (x : Q) : WalkComponent T :=
  Quotient.mk _ x

/-- A displayed augmented walk puts its endpoints in the same component. -/
theorem walkComponentClass_eq_of_walk (T : RightMeshData Q) {x y : Q}
    (p : Walk T x y) :
    walkComponentClass T x = walkComponentClass T y :=
  Quotient.sound ⟨p⟩

/-- Equality of component classes supplies an augmented walk between the
chosen representatives. -/
theorem nonempty_walk_of_walkComponentClass_eq
    (T : RightMeshData Q) {x y : Q}
    (h : walkComponentClass T x = walkComponentClass T y) :
    WalkConnected T x y :=
  Quotient.exact h

/-- The endpoints of an ordinary quiver arrow lie in the same walk
component. -/
theorem walkComponentClass_eq_of_arrow
    (T : RightMeshData Q) {x y : Q} (a : x ⟶ y) :
    walkComponentClass T x = walkComponentClass T y :=
  walkComponentClass_eq_of_walk T (oldArrowPath T a)

/-- A nonprojective vertex and its translate lie in the same walk component. -/
theorem walkComponentClass_tau
    (T : RightMeshData Q) (x : {x : Q // x ∉ T.projective}) :
    walkComponentClass T x.1 = walkComponentClass T (T.tau x) :=
  walkComponentClass_eq_of_walk T (meshArrowPath T x)

/-- Distinct walk components have no ordinary arrows between them. -/
theorem isEmpty_arrow_of_walkComponentClass_ne
    (T : RightMeshData Q) {x y : Q}
    (h : walkComponentClass T x ≠ walkComponentClass T y) :
    IsEmpty (x ⟶ y) :=
  ⟨fun a ↦ h (walkComponentClass_eq_of_arrow T a)⟩

/-- The full subquiver on the vertices of one augmented-walk component. -/
abbrev WalkComponentVertex (T : RightMeshData Q) (c : WalkComponent T) :=
  {x : Q // walkComponentClass T x = c}

instance walkComponentQuiver (T : RightMeshData Q) (c : WalkComponent T) :
    Quiver (WalkComponentVertex T c) where
  Hom x y := x.1 ⟶ y.1

/-- Forgetting the component witness includes a walk component into the
ambient quiver. -/
def walkComponentInclusion (T : RightMeshData Q) (c : WalkComponent T) :
    WalkComponentVertex T c ⥤q Q where
  obj := Subtype.val
  map := id

@[simp]
theorem walkComponentInclusion_obj
    (T : RightMeshData Q) (c : WalkComponent T)
    (x : WalkComponentVertex T c) :
    (walkComponentInclusion T c).obj x = x.1 :=
  rfl

@[simp]
theorem walkComponentInclusion_map
    (T : RightMeshData Q) (c : WalkComponent T)
    {x y : WalkComponentVertex T c} (a : x ⟶ y) :
    (walkComponentInclusion T c).map a = a :=
  rfl

/-- Restricting the projective boundary, translation, and polarization gives
right-mesh data on every augmented-walk component. -/
def walkComponentRightMeshData
    (T : RightMeshData Q) (c : WalkComponent T) :
    RightMeshData (WalkComponentVertex T c) where
  projective := {x | x.1 ∈ T.projective}
  tau := fun x ↦
    ⟨T.tau ⟨x.1.1, x.2⟩,
      (walkComponentClass_tau T ⟨x.1.1, x.2⟩).symm.trans x.1.2⟩
  arrowEquiv := fun x y ↦ T.arrowEquiv ⟨x.1.1, x.2⟩ y.1

@[simp]
theorem walkComponentRightMeshData_projective_iff
    (T : RightMeshData Q) (c : WalkComponent T)
    (x : WalkComponentVertex T c) :
    x ∈ (walkComponentRightMeshData T c).projective ↔ x.1 ∈ T.projective :=
  Iff.rfl

@[simp]
theorem walkComponentRightMeshData_tau_val
    (T : RightMeshData Q) (c : WalkComponent T)
    (x : {x : WalkComponentVertex T c //
      x ∉ (walkComponentRightMeshData T c).projective}) :
    ((walkComponentRightMeshData T c).tau x).1 =
      T.tau ⟨x.1.1, x.2⟩ :=
  rfl

/-- The endpoints of any positive or negative augmented arrow lie in the
same walk component. -/
theorem walkComponentClass_eq_of_symmetricAugmentedArrow
    (T : RightMeshData Q) {x y : Q}
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) x y) :
    walkComponentClass T x = walkComponentClass T y := by
  rcases e with e | e
  · rcases e with a | s
    · exact walkComponentClass_eq_of_arrow T a
    · exact walkComponentClass_tau T s
  · rcases e with a | s
    · exact (walkComponentClass_eq_of_arrow T a).symm
    · exact (walkComponentClass_tau T s).symm

/-- A symmetric augmented arrow whose endpoints lie in one component lifts
to the induced symmetric augmented quiver. -/
theorem nonempty_walkComponentSymmetricArrow
    (T : RightMeshData Q) (c : WalkComponent T) {x y : Q}
    (hx : walkComponentClass T x = c)
    (hy : walkComponentClass T y = c)
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) x y) :
    Nonempty
      (@Quiver.Hom
        (Quiver.Symmetrify
          (AugmentedVertex (walkComponentRightMeshData T c)))
        (Quiver.symmetrifyQuiver
          (AugmentedVertex (walkComponentRightMeshData T c)))
        (⟨x, hx⟩ : WalkComponentVertex T c)
        (⟨y, hy⟩ : WalkComponentVertex T c)) := by
  let D := walkComponentRightMeshData T c
  rcases e with e | e
  · rcases e with a | s
    · exact ⟨Sum.inl (AugmentedArrow.old a)⟩
    · let sc : {z : WalkComponentVertex T c // z ∉ D.projective} :=
        ⟨⟨s.1, hx⟩, s.2⟩
      have ht : D.tau sc = ⟨T.tau s, hy⟩ := by
        apply Subtype.ext
        rfl
      exact ⟨Quiver.Hom.cast rfl ht (Sum.inl (AugmentedArrow.mesh sc))⟩
  · rcases e with a | s
    · exact ⟨Sum.inr (AugmentedArrow.old a)⟩
    · let sc : {z : WalkComponentVertex T c // z ∉ D.projective} :=
        ⟨⟨s.1, hy⟩, s.2⟩
      have ht : D.tau sc = ⟨T.tau s, hx⟩ := by
        apply Subtype.ext
        rfl
      exact ⟨Quiver.Hom.cast ht rfl (Sum.inr (AugmentedArrow.mesh sc))⟩

/-- An ambient augmented walk whose endpoints lie in one component lifts to
an augmented walk in the induced right-mesh data. -/
theorem nonempty_walkComponentWalk_of_walk
    (T : RightMeshData Q) (c : WalkComponent T) {x y : Q}
    (p : Walk T x y)
    (hx : walkComponentClass T x = c)
    (hy : walkComponentClass T y = c) :
    Nonempty
      (Walk (walkComponentRightMeshData T c)
        (⟨x, hx⟩ : WalkComponentVertex T c)
        (⟨y, hy⟩ : WalkComponentVertex T c)) := by
  induction p with
  | nil => exact ⟨Quiver.Path.nil⟩
  | @cons z y p e ih =>
      have hz : walkComponentClass T z = c :=
        (walkComponentClass_eq_of_walk T p).symm.trans hx
      exact ⟨(ih hz).some.cons
        (nonempty_walkComponentSymmetricArrow T c hz hy e).some⟩

/-- Every induced augmented-walk component is connected from any of its
vertices. -/
theorem walkComponent_isWalkConnectedAt
    (T : RightMeshData Q) (c : WalkComponent T)
    (x₀ : WalkComponentVertex T c) :
    IsWalkConnectedAt (walkComponentRightMeshData T c) x₀ := by
  intro y
  obtain ⟨p⟩ := nonempty_walk_of_walkComponentClass_eq T
    (x₀.2.trans y.2.symm)
  exact nonempty_walkComponentWalk_of_walk T c p x₀.2 y.2

/-- Every walk component has a vertex representative. -/
theorem walkComponentVertex_nonempty
    (T : RightMeshData Q) (c : WalkComponent T) :
    Nonempty (WalkComponentVertex T c) :=
  ⟨⟨Quotient.out c, Quotient.out_eq c⟩⟩

/-- The endpoints of an ordinary quiver path lie in the same augmented-walk
component. -/
theorem walkComponentClass_eq_of_path
    (T : RightMeshData Q) {x y : Q} (p : Quiver.Path x y) :
    walkComponentClass T x = walkComponentClass T y := by
  induction p with
  | nil => rfl
  | cons p a ih => exact ih.trans (walkComponentClass_eq_of_arrow T a)

/-- Distinct augmented-walk components admit no ordinary quiver paths
between them. -/
theorem isEmpty_path_of_walkComponentClass_ne
    (T : RightMeshData Q) {x y : Q}
    (h : walkComponentClass T x ≠ walkComponentClass T y) :
    IsEmpty (Quiver.Path x y) :=
  ⟨fun p ↦ h (walkComponentClass_eq_of_path T p)⟩

variable {k : Type u} [Field k]

/-- Every free-linear-path morphism between distinct augmented-walk
components is zero. -/
theorem linearPathCategory_hom_eq_zero_of_walkComponentClass_ne
    (T : RightMeshData Q) {x y : Q}
    (h : walkComponentClass T x ≠ walkComponentClass T y)
    (f : MagnitudeConjecture.LinearPathCategory.obj k Q x ⟶
      MagnitudeConjecture.LinearPathCategory.obj k Q y) :
    f = 0 := by
  apply (MagnitudeConjecture.LinearPathCategory.homPathLinearEquiv _ _).injective
  ext p
  exact False.elim
    ((isEmpty_path_of_walkComponentClass_ne T h.symm).false p)

/-- Every mesh-category morphism between distinct augmented-walk components
is zero. -/
theorem meshCategory_hom_eq_zero_of_walkComponentClass_ne
    (T : RightMeshData Q) [∀ x : Q, Fintype (Σ y : Q, x ⟶ y)]
    {x y : Q} (h : walkComponentClass T x ≠ walkComponentClass T y)
    (f : MeshCategory.obj (k := k) T x ⟶ MeshCategory.obj (k := k) T y) :
    f = 0 := by
  obtain ⟨g, hg⟩ :=
    MagnitudeConjecture.LinearPathCategory.HomogeneousQuotient.quotientHom_surjective
      (T.meshGeneratorSet (k := k))
      (MagnitudeConjecture.LinearPathCategory.obj k Q x)
      (MagnitudeConjecture.LinearPathCategory.obj k Q y) f
  have hg0 : g = 0 :=
    linearPathCategory_hom_eq_zero_of_walkComponentClass_ne T h g
  rw [← hg, hg0]
  exact LinearMap.map_zero _

/-- A finite translation quiver has finitely many augmented-walk
components. -/
noncomputable instance walkComponentFintype
    (T : RightMeshData Q) [Fintype Q] : Fintype (WalkComponent T) := by
  classical
  exact Quotient.fintype (walkComponentSetoid T)

end MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover
