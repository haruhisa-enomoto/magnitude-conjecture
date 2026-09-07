import MagnitudeConjecture.CategoryTheory.MeshIdealLifting
import Mathlib.Combinatorics.Quiver.Symmetric

/-!
# Universal covers of polarized right translation quivers

Following Bongartz--Gabriel, the universal-cover vertices are homotopy classes
of walks from a fixed base vertex.  The walk quiver augments the ordinary
arrows by one formal mesh edge from each nonprojective vertex to its translate.
Homotopy cancels an arrow with its formal inverse and identifies a formal mesh
edge with every polarized length-two route through that mesh.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.MeshCategory.RightMeshData

universe v w

variable {Q : Type v} [Quiver.{w} Q]

namespace UniversalCover

/-- A type synonym on which the augmented walk quiver is installed without
replacing the original quiver structure on Q. -/
def AugmentedVertex (_T : RightMeshData Q) := Q

/-- The augmented arrows: ordinary arrows and one formal degree-two edge from
each nonprojective vertex to its translate. -/
inductive AugmentedArrow (T : RightMeshData Q) :
    AugmentedVertex T → AugmentedVertex T → Type max v w
  | old {x y : Q} (a : x ⟶ y) : AugmentedArrow T x y
  | mesh (x : {x : Q // x ∉ T.projective}) :
      AugmentedArrow T x.1 (T.tau x)

instance augmentedQuiver (T : RightMeshData Q) :
    Quiver (AugmentedVertex T) where
  Hom := AugmentedArrow T

/-- An ordinary arrow regarded as a positive arrow of the symmetrified
augmented quiver. -/
def oldArrow (T : RightMeshData Q) {x y : Q} (a : x ⟶ y) :
    @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) x y :=
  Sum.inl (AugmentedArrow.old a)

/-- The formal mesh edge regarded as a positive arrow of the symmetrified
augmented quiver. -/
def meshArrow (T : RightMeshData Q)
    (x : {x : Q // x ∉ T.projective}) :
    @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) x.1 (T.tau x) :=
  Sum.inl (AugmentedArrow.mesh x)

/-- The one-edge walk associated with an ordinary arrow. -/
def oldArrowPath (T : RightMeshData Q) {x y : Q} (a : x ⟶ y) :
    @Quiver.Path (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) x y :=
  @Quiver.Hom.toPath _ (Quiver.symmetrifyQuiver (AugmentedVertex T))
    _ _ (oldArrow T a)

/-- The one-edge walk associated with a formal mesh edge. -/
def meshArrowPath (T : RightMeshData Q)
    (x : {x : Q // x ∉ T.projective}) :
    @Quiver.Path (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) x.1 (T.tau x) :=
  @Quiver.Hom.toPath _ (Quiver.symmetrifyQuiver (AugmentedVertex T))
    _ _ (meshArrow T x)

/-- Walks in the symmetrified augmented quiver from a fixed base vertex. -/
abbrev Walk (T : RightMeshData Q) (x₀ y : Q) :=
  @Quiver.Path (Quiver.Symmetrify (AugmentedVertex T))
    (Quiver.symmetrifyQuiver (AugmentedVertex T)) x₀ y

/-- Bongartz--Gabriel homotopy of augmented walks with fixed endpoints. -/
inductive Homotopic (T : RightMeshData Q) (x₀ : Q) :
    {y : Q} → Walk T x₀ y → Walk T x₀ y → Prop
  | refl {y : Q} (p : Walk T x₀ y) : Homotopic T x₀ p p
  | symm {y : Q} {p q : Walk T x₀ y} :
      Homotopic T x₀ p q → Homotopic T x₀ q p
  | trans {y : Q} {p q r : Walk T x₀ y} :
      Homotopic T x₀ p q → Homotopic T x₀ q r → Homotopic T x₀ p r
  | comp {y z : Q} {p q : Walk T x₀ y}
      (h : Homotopic T x₀ p q)
      (r : @Quiver.Path (Quiver.Symmetrify (AugmentedVertex T))
        (Quiver.symmetrifyQuiver (AugmentedVertex T)) y z) :
      Homotopic T x₀ (p.comp r) (q.comp r)
  | cancel {y z : Q} (p : Walk T x₀ y)
      (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
        (Quiver.symmetrifyQuiver (AugmentedVertex T)) y z) :
      Homotopic T x₀
        ((p.comp e.toPath).comp (Quiver.reverse e).toPath) p
  | mesh (s : {s : Q // s ∉ T.projective})
      (p : Walk T x₀ s.1)
      (a : T.MeshArrow s) :
      Homotopic T x₀
        (p.comp (meshArrowPath T s))
        ((p.comp (oldArrowPath T a.2)).comp
          (oldArrowPath T ((T.arrowEquiv s a.1) a.2)))

/-- Augmented-walk homotopy as a setoid at one endpoint. -/
def homotopySetoid (T : RightMeshData Q) (x₀ y : Q) :
    Setoid (Walk T x₀ y) where
  r := Homotopic T x₀
  iseqv :=
    { refl := Homotopic.refl
      symm := Homotopic.symm
      trans := Homotopic.trans }

/-- Vertices of the universal cover based at x₀: an endpoint together with
a homotopy class of walks from x₀ to that endpoint. -/
def Vertex (T : RightMeshData Q) (x₀ : Q) :=
  Σ y : Q, Quotient (homotopySetoid T x₀ y)

/-- Projection of a universal-cover vertex to its endpoint downstairs. -/
def vertex (T : RightMeshData Q) (x₀ : Q) : Vertex T x₀ → Q :=
  Sigma.fst

/-- Append one symmetric augmented arrow to a universal-cover vertex. -/
def extend (T : RightMeshData Q) (x₀ : Q)
    (W : Vertex T x₀) {z : Q}
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) W.1 z) :
    Vertex T x₀ :=
  ⟨z, Quotient.map
    (fun p ↦ p.comp e.toPath)
    (fun _ _ h ↦ Homotopic.comp h e.toPath) W.2⟩

/-- Transporting the target witness of an appended arrow does not change the
resulting universal-cover vertex. -/
theorem extend_cast_target (T : RightMeshData Q) (x₀ : Q)
    (W : Vertex T x₀) {z z' : Q}
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) W.1 z)
    (h : z = z') :
    extend T x₀ W (Quiver.Hom.cast rfl h e) = extend T x₀ W e := by
  subst z'
  rfl

@[simp]
theorem extend_vertex (T : RightMeshData Q) (x₀ : Q)
    (W : Vertex T x₀) {z : Q}
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) W.1 z) :
    (extend T x₀ W e).1 = z :=
  rfl

/-- Appending an arrow and then its formal inverse does not change a cover
vertex. -/
theorem extend_reverse (T : RightMeshData Q) (x₀ : Q)
    (W : Vertex T x₀) {z : Q}
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) W.1 z) :
    extend T x₀ (extend T x₀ W e) (Quiver.reverse e) = W := by
  rcases W with ⟨y, W⟩
  induction W using Quotient.inductionOn with
  | _ p =>
      apply Sigma.ext (by rfl)
      apply heq_of_eq
      exact Quotient.sound (Homotopic.cancel p e)

/-- Appending a formal inverse and then the original arrow does not change a
cover vertex. -/
theorem extend_reverse_left (T : RightMeshData Q) (x₀ : Q)
    (W : Vertex T x₀) {z : Q}
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) z W.1) :
    extend T x₀ (extend T x₀ W (Quiver.reverse e)) e = W := by
  simpa using extend_reverse T x₀ W (Quiver.reverse e)

/-- A formal mesh edge and every polarized length-two mesh route have the same
endpoint in the universal cover. -/
theorem extend_mesh (T : RightMeshData Q) (x₀ : Q)
    (W : Vertex T x₀)
    (s : {s : Q // s ∉ T.projective}) (hs : W.1 = s.1)
    (a : T.MeshArrow s) :
    extend T x₀ W ((meshArrow T s).cast hs.symm rfl) =
      extend T x₀
        (extend T x₀ W ((oldArrow T a.2).cast hs.symm rfl))
        (oldArrow T ((T.arrowEquiv s a.1) a.2)) := by
  rcases W with ⟨y, W⟩
  change y = s.1 at hs
  subst y
  induction W using Quotient.inductionOn with
  | _ p =>
      apply Sigma.ext (by rfl)
      apply heq_of_eq
      exact Quotient.sound (Homotopic.mesh s p a)

/-- Lift an ordinary arrow by appending it to a walk class. -/
def extendOld (T : RightMeshData Q) (x₀ : Q)
    (W : Vertex T x₀) {z : Q} (a : W.1 ⟶ z) : Vertex T x₀ :=
  extend T x₀ W (oldArrow T a)

/-- The source of a lifted ordinary arrow is recovered by appending the
formal inverse to its target. -/
theorem source_eq_reverse_extend (T : RightMeshData Q) (x₀ : Q)
    (Z W : Vertex T x₀) (a : Z.1 ⟶ W.1)
    (ha : extendOld T x₀ Z a = W) :
    Z = extend T x₀ W (Quiver.reverse (oldArrow T a)) := by
  let A : Σ V : Vertex T x₀, Quiver.Costar V.1 :=
    ⟨extendOld T x₀ Z a, ⟨Z.1, a⟩⟩
  let B : Σ V : Vertex T x₀, Quiver.Costar V.1 :=
    ⟨W, ⟨Z.1, a⟩⟩
  have hAB : A = B := by
    apply Sigma.ext ha
    rfl
  calc
    Z = extend T x₀ A.1 (Quiver.reverse (oldArrow T A.2.2)) :=
      (extend_reverse T x₀ Z (oldArrow T a)).symm
    _ = extend T x₀ B.1 (Quiver.reverse (oldArrow T B.2.2)) :=
      congrArg
        (fun E : Σ V : Vertex T x₀, Quiver.Costar V.1 ↦
          extend T x₀ E.1 (Quiver.reverse (oldArrow T E.2.2))) hAB
    _ = extend T x₀ W (Quiver.reverse (oldArrow T a)) := rfl

/-- Arrows of the universal cover are the unique ordinary-arrow lifts with a
specified endpoint. -/
def Hom (T : RightMeshData Q) (x₀ : Q) (W Z : Vertex T x₀) :=
  {a : W.1 ⟶ Z.1 // extendOld T x₀ W a = Z}

instance quiver (T : RightMeshData Q) (x₀ : Q) :
    Quiver (Vertex T x₀) where
  Hom := Hom T x₀

/-- Projection from the universal-cover quiver to the original quiver. -/
def projection (T : RightMeshData Q) (x₀ : Q) : Vertex T x₀ ⥤q Q where
  obj := vertex T x₀
  map := Subtype.val

theorem projection_star_bijective (T : RightMeshData Q) (x₀ : Q)
    (W : Vertex T x₀) :
    Function.Bijective ((projection T x₀).star W) := by
  constructor
  · rintro ⟨Z, a⟩ ⟨Z', a'⟩ h
    change (⟨Z.1, a.1⟩ : Quiver.Star W.1) =
      (⟨Z'.1, a'.1⟩ : Quiver.Star W.1) at h
    have hZ : Z = Z' := by
      calc
        Z = extendOld T x₀ W a.1 := a.2.symm
        _ = extendOld T x₀ W a'.1 := congrArg
          (fun A : Quiver.Star W.1 ↦ extendOld T x₀ W A.2) h
        _ = Z' := a'.2
    subst Z'
    have ha : a.1 = a'.1 := eq_of_heq (Sigma.ext_iff.mp h).2
    have haa : a = a' := Subtype.ext ha
    subst a'
    rfl
  · rintro ⟨z, a⟩
    let Z := extendOld T x₀ W a
    exact ⟨⟨Z, ⟨a, rfl⟩⟩, rfl⟩

theorem projection_costar_bijective (T : RightMeshData Q) (x₀ : Q)
    (W : Vertex T x₀) :
    Function.Bijective ((projection T x₀).costar W) := by
  constructor
  · rintro ⟨Z, a⟩ ⟨Z', a'⟩ h
    change (⟨Z.1, a.1⟩ : Quiver.Costar W.1) =
      (⟨Z'.1, a'.1⟩ : Quiver.Costar W.1) at h
    have hZ : Z = Z' := by
      calc
        Z = extend T x₀ W (Quiver.reverse (oldArrow T a.1)) :=
          source_eq_reverse_extend T x₀ Z W a.1 a.2
        _ = extend T x₀ W (Quiver.reverse (oldArrow T a'.1)) := congrArg
          (fun A : Quiver.Costar W.1 ↦
            extend T x₀ W (Quiver.reverse (oldArrow T A.2))) h
        _ = Z' :=
          (source_eq_reverse_extend T x₀ Z' W a'.1 a'.2).symm
    subst Z'
    have ha : a.1 = a'.1 := eq_of_heq (Sigma.ext_iff.mp h).2
    have haa : a = a' := Subtype.ext ha
    subst a'
    rfl
  · rintro ⟨z, a⟩
    let Z := extend T x₀ W (Quiver.reverse (oldArrow T a))
    have hZW : extendOld T x₀ Z a = W := by
      exact extend_reverse_left T x₀ W (oldArrow T a)
    exact ⟨⟨Z, ⟨a, hZW⟩⟩, rfl⟩

/-- The endpoint projection is a quiver covering. -/
theorem projection_isCovering (T : RightMeshData Q) (x₀ : Q) :
    (projection T x₀).IsCovering where
  star_bijective := projection_star_bijective T x₀
  costar_bijective := projection_costar_bijective T x₀

/-- Projective vertices in the universal cover are exactly those lying over
projective vertices downstairs. -/
def projectiveSet (T : RightMeshData Q) (x₀ : Q) : Set (Vertex T x₀) :=
  {W | W.1 ∈ T.projective}

/-- The downstairs nonprojective vertex underlying a nonprojective
universal-cover vertex. -/
def baseNonprojective (T : RightMeshData Q) (x₀ : Q)
    (W : {W : Vertex T x₀ // W ∉ projectiveSet T x₀}) :
    {x : Q // x ∉ T.projective} :=
  ⟨W.1.1, W.2⟩

/-- Translation in the universal cover is obtained by appending the formal
mesh edge. -/
def tau (T : RightMeshData Q) (x₀ : Q)
    (W : {W : Vertex T x₀ // W ∉ projectiveSet T x₀}) : Vertex T x₀ :=
  extend T x₀ W.1 (meshArrow T (baseNonprojective T x₀ W))

/-- Lift the polarized partner of one arrow in a universal-cover mesh. -/
def pairedArrow (T : RightMeshData Q) (x₀ : Q)
    (W : {W : Vertex T x₀ // W ∉ projectiveSet T x₀})
    (Y : Vertex T x₀) (a : W.1 ⟶ Y) : Y ⟶ tau T x₀ W := by
  let s := baseNonprojective T x₀ W
  let b : Y.1 ⟶ T.tau s := (T.arrowEquiv s Y.1) a.1
  have hm := extend_mesh T x₀ W.1 s rfl ⟨Y.1, a.1⟩
  change tau T x₀ W = extendOld T x₀ (extendOld T x₀ W.1 a.1) b at hm
  let E : Σ V : Vertex T x₀, Quiver.Star V.1 :=
    ⟨extendOld T x₀ W.1 a.1, ⟨T.tau s, b⟩⟩
  let F : Σ V : Vertex T x₀, Quiver.Star V.1 :=
    ⟨Y, ⟨T.tau s, b⟩⟩
  have hEF : E = F := by
    apply Sigma.ext a.2
    rfl
  have hextend : extendOld T x₀ (extendOld T x₀ W.1 a.1) b =
      extendOld T x₀ Y b :=
    congrArg
      (fun D : Σ V : Vertex T x₀, Quiver.Star V.1 ↦
        extendOld T x₀ D.1 D.2.2) hEF
  exact ⟨b, hextend.symm.trans hm.symm⟩

theorem pairedArrow_val (T : RightMeshData Q) (x₀ : Q)
    (W : {W : Vertex T x₀ // W ∉ projectiveSet T x₀})
    (Y : Vertex T x₀) (a : W.1 ⟶ Y) :
    (pairedArrow T x₀ W Y a).1 =
      (T.arrowEquiv (baseNonprojective T x₀ W) Y.1) a.1 := by
  rfl

theorem pairedArrow_injective (T : RightMeshData Q) (x₀ : Q)
    (W : {W : Vertex T x₀ // W ∉ projectiveSet T x₀})
    (Y : Vertex T x₀) :
    Function.Injective (pairedArrow T x₀ W Y) := by
  intro a b hab
  apply (projection_isCovering T x₀).map_injective
  change a.1 = b.1
  have hval := congrArg Subtype.val hab
  change
    (T.arrowEquiv (baseNonprojective T x₀ W) Y.1) a.1 =
      (T.arrowEquiv (baseNonprojective T x₀ W) Y.1) b.1 at hval
  exact (T.arrowEquiv (baseNonprojective T x₀ W) Y.1).injective hval

set_option backward.isDefEq.respectTransparency false in
theorem pairedArrow_surjective (T : RightMeshData Q) (x₀ : Q)
    (W : {W : Vertex T x₀ // W ∉ projectiveSet T x₀})
    (Y : Vertex T x₀) :
    Function.Surjective (pairedArrow T x₀ W Y) := by
  intro c
  let s := baseNonprojective T x₀ W
  let a₀ : W.1.1 ⟶ Y.1 := (T.arrowEquiv s Y.1).symm c.1
  obtain ⟨⟨Z, a⟩, ha⟩ :=
    (projection_star_bijective T x₀ W.1).2
      (show Quiver.Star W.1.1 from ⟨Y.1, a₀⟩)
  change (⟨Z.1, a.1⟩ : Quiver.Star W.1.1) = ⟨Y.1, a₀⟩ at ha
  have hbase :
      (projection T x₀).costar (tau T x₀ W)
          ⟨Z, pairedArrow T x₀ W Z a⟩ =
        (projection T x₀).costar (tau T x₀ W) ⟨Y, c⟩ := by
    change (⟨Z.1, (pairedArrow T x₀ W Z a).1⟩ :
        Quiver.Costar (T.tau s)) = ⟨Y.1, c.1⟩
    have hpolarized := congrArg
      (fun A : Quiver.Star W.1.1 ↦
        (⟨A.1, (T.arrowEquiv s A.1) A.2⟩ :
          Quiver.Costar (T.tau s))) ha
    simpa only [pairedArrow_val, a₀, Equiv.apply_symm_apply] using hpolarized
  have hcover :
      (⟨Z, pairedArrow T x₀ W Z a⟩ :
        Quiver.Costar (tau T x₀ W)) = ⟨Y, c⟩ :=
    (projection_costar_bijective T x₀ (tau T x₀ W)).1 hbase
  cases hcover
  exact ⟨a, rfl⟩

/-- Polarization of the lifted mesh, obtained from mesh homotopy and the
local star/costar uniqueness of the quiver cover. -/
def arrowEquiv (T : RightMeshData Q) (x₀ : Q)
    (W : {W : Vertex T x₀ // W ∉ projectiveSet T x₀})
    (Y : Vertex T x₀) :
    (W.1 ⟶ Y) ≃ (Y ⟶ tau T x₀ W) :=
  Equiv.ofBijective (pairedArrow T x₀ W Y)
    ⟨pairedArrow_injective T x₀ W Y,
      pairedArrow_surjective T x₀ W Y⟩

@[simp]
theorem arrowEquiv_apply (T : RightMeshData Q) (x₀ : Q)
    (W : {W : Vertex T x₀ // W ∉ projectiveSet T x₀})
    (Y : Vertex T x₀) (a : W.1 ⟶ Y) :
    arrowEquiv T x₀ W Y a = pairedArrow T x₀ W Y a :=
  rfl

/-- The polarized right-mesh data lifted to the universal-cover quiver. -/
def rightMeshData (T : RightMeshData Q) (x₀ : Q) :
    RightMeshData (Vertex T x₀) where
  projective := projectiveSet T x₀
  tau := tau T x₀
  arrowEquiv := arrowEquiv T x₀

/-- The endpoint projection, together with the lifted translation and
polarization, is a covering of polarized right translation quivers. -/
def cover (T : RightMeshData Q) (x₀ : Q) :
    RightMeshData.Cover (rightMeshData T x₀) T where
  toPrefunctor := projection T x₀
  isCovering := projection_isCovering T x₀
  map_projective_iff := fun _ ↦ Iff.rfl
  map_tau := fun _ ↦ rfl
  map_arrowEquiv := by
    intro W Y a
    rfl

universe u

/-- The universal-cover projection induces a Bongartz--Gabriel covering
functor between the associated raw mesh categories. -/
theorem meshFunctor_isCovering (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)] :
    let C := cover T x₀
    letI := C.sourceStarFintype
    MagnitudeConjecture.LinearCovering.IsCovering
      (k := k) (C.functor (k := k)) := by
  let C := cover T x₀
  letI := C.sourceStarFintype
  exact C.functor_isCovering (k := k)

end UniversalCover

end MagnitudeConjecture.MeshCategory.RightMeshData
