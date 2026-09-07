import MagnitudeConjecture.CategoryTheory.TranslationQuiverUniversalCover
import MagnitudeConjecture.CategoryTheory.DeckShiftAction
import MagnitudeConjecture.Combinatorics.OrbitQuotientAction

/-!
# Deck transformations of the universal translation-quiver cover

The fundamental group consists of homotopy classes of closed augmented walks
at the chosen base vertex.  Prepending such a loop gives the deck action on
the based-walk universal cover.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover

universe v w

variable {Q : Type v} [Quiver.{w} Q]

/-- Formal reversal with the symmetrified augmented-quiver instance fixed
explicitly. -/
def reverseWalk (T : RightMeshData Q) {x y : Q} (p : Walk T x y) :
    Walk T y x :=
  @Quiver.Path.reverse (Quiver.Symmetrify (AugmentedVertex T))
    (Quiver.symmetrifyQuiver (AugmentedVertex T)) _ x y p

@[simp]
theorem reverseWalk_comp (T : RightMeshData Q) {x y z : Q}
    (p : Walk T x y) (q : Walk T y z) :
    reverseWalk T (p.comp q) =
      (reverseWalk T q).comp (reverseWalk T p) :=
  @Quiver.Path.reverse_comp (Quiver.Symmetrify (AugmentedVertex T))
    (Quiver.symmetrifyQuiver (AugmentedVertex T)) _ x y z p q

@[simp]
theorem reverseWalk_toPath (T : RightMeshData Q) {x y : Q}
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) x y) :
    reverseWalk T e.toPath = (Quiver.reverse e).toPath :=
  rfl

@[simp]
theorem reverseWalk_cons (T : RightMeshData Q) {x y z : Q}
    (p : Walk T x y)
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) y z) :
    reverseWalk T (p.cons e) =
      (Quiver.reverse e).toPath.comp (reverseWalk T p) :=
  rfl

theorem comp_toPath_eq_consWalk (T : RightMeshData Q) {x y z : Q}
    (p : Walk T x y)
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) y z) :
    p.comp e.toPath = p.cons e :=
  @Quiver.Path.comp_toPath_eq_cons
    (Quiver.Symmetrify (AugmentedVertex T))
    (Quiver.symmetrifyQuiver (AugmentedVertex T)) x y z p e

/-- Composition with the symmetrified augmented-quiver instance fixed
explicitly. -/
def compWalk (T : RightMeshData Q) {x y z : Q}
    (p : Walk T x y) (q : Walk T y z) : Walk T x z :=
  @Quiver.Path.comp (Quiver.Symmetrify (AugmentedVertex T))
    (Quiver.symmetrifyQuiver (AugmentedVertex T)) x y z p q

@[simp]
theorem reverseWalk_reverseWalk (T : RightMeshData Q) {x y : Q}
    (p : Walk T x y) : reverseWalk T (reverseWalk T p) = p :=
  @Quiver.Path.reverse_reverse (Quiver.Symmetrify (AugmentedVertex T))
    (Quiver.symmetrifyQuiver (AugmentedVertex T)) _ x y p

/-- Augmented-walk homotopy is also compatible with composition on the left,
with the base point changed to the source of the prefix. -/
theorem Homotopic.left_comp (T : RightMeshData Q) {x₀ y z : Q}
    {p q : Walk T x₀ y} (s : Walk T z x₀)
    (h : Homotopic T x₀ p q) :
    Homotopic T z (s.comp p) (s.comp q) := by
  induction h with
  | refl p => exact Homotopic.refl _
  | symm _ ih => exact Homotopic.symm ih
  | trans _ _ ih₁ ih₂ => exact Homotopic.trans ih₁ ih₂
  | comp h r ih =>
      simpa only [Quiver.Path.comp_assoc] using Homotopic.comp ih r
  | cancel p e =>
      simpa only [Quiver.Path.comp_assoc] using
        Homotopic.cancel (s.comp p) e
  | mesh x p a =>
      simpa only [Quiver.Path.comp_assoc] using
        Homotopic.mesh x (s.comp p) a

set_option backward.isDefEq.respectTransparency false in
/-- A path followed by its formal reverse cancels inside any prefixed walk. -/
theorem Homotopic.comp_reverse (T : RightMeshData Q) {x₀ y z : Q}
    (s : Walk T x₀ y) (p : Walk T y z) :
    Homotopic T x₀ ((s.comp p).comp (reverseWalk T p)) s := by
  induction p with
  | nil => exact Homotopic.refl _
  | cons p e ih =>
      rw [reverseWalk_cons, ← comp_toPath_eq_consWalk T p e]
      simpa only [Quiver.Path.comp_assoc] using
        Homotopic.trans
          (Homotopic.comp
            (Homotopic.cancel (T := T) (x₀ := x₀) (s.comp p) e)
            (reverseWalk T p)) ih

/-- The formal reverse of a path followed by that path also cancels inside
any prefixed walk. -/
theorem Homotopic.reverse_comp (T : RightMeshData Q) {x₀ y z : Q}
    (s : Walk T x₀ z) (p : Walk T y z) :
    Homotopic T x₀ ((s.comp (reverseWalk T p)).comp p) s := by
  simpa only [reverseWalk_reverseWalk] using
    Homotopic.comp_reverse T s (reverseWalk T p)

/-- Reversing augmented walks preserves their homotopy class, while changing
the base point from their common source to their common endpoint. -/
theorem Homotopic.reverse (T : RightMeshData Q) {x₀ y : Q}
    {p q : Walk T x₀ y} (h : Homotopic T x₀ p q) :
    Homotopic T y (reverseWalk T p) (reverseWalk T q) := by
  have hpq :
      Homotopic T x₀ (p.comp (reverseWalk T q)) Quiver.Path.nil :=
    Homotopic.trans (Homotopic.comp h (reverseWalk T q))
      (by simpa only [Quiver.Path.nil_comp] using
        Homotopic.comp_reverse T Quiver.Path.nil q)
  have hpre :
      Homotopic T y
        ((reverseWalk T p).comp (p.comp (reverseWalk T q)))
        (reverseWalk T p) :=
    Homotopic.left_comp T (reverseWalk T p) hpq
  have hcancel :
      Homotopic T y
        ((reverseWalk T p).comp (p.comp (reverseWalk T q)))
        (reverseWalk T q) := by
    simpa only [Quiver.Path.comp_assoc, Quiver.Path.nil_comp] using
      Homotopic.comp
        (Homotopic.reverse_comp T Quiver.Path.nil p) (reverseWalk T q)
  exact Homotopic.symm (Homotopic.trans (Homotopic.symm hcancel) hpre)

/-- The fundamental group at `x₀`: homotopy classes of closed augmented
walks based at `x₀`. -/
def FundamentalGroup (T : RightMeshData Q) (x₀ : Q) :=
  Quotient (homotopySetoid T x₀ x₀)

/-- The fundamental-group class of one based loop. -/
def loopClass (T : RightMeshData Q) (x₀ : Q) (p : Walk T x₀ x₀) :
    FundamentalGroup T x₀ :=
  Quotient.mk _ p

/-- Composition of based loops descends to homotopy classes. -/
def loopMul (T : RightMeshData Q) (x₀ : Q) :
    FundamentalGroup T x₀ → FundamentalGroup T x₀ →
      FundamentalGroup T x₀ :=
  Quotient.map₂ (compWalk T) fun _p p' hp q _q' hq ↦
    Homotopic.trans (Homotopic.comp hp q)
      (Homotopic.left_comp T p' hq)

/-- Reversal of based loops descends to homotopy classes. -/
def loopInv (T : RightMeshData Q) (x₀ : Q) :
    FundamentalGroup T x₀ → FundamentalGroup T x₀ :=
  Quotient.map (reverseWalk T) fun _ _ h ↦ Homotopic.reverse T h

instance fundamentalGroupMul (T : RightMeshData Q) (x₀ : Q) :
    Mul (FundamentalGroup T x₀) :=
  ⟨loopMul T x₀⟩

instance fundamentalGroupOne (T : RightMeshData Q) (x₀ : Q) :
    One (FundamentalGroup T x₀) :=
  ⟨loopClass T x₀ Quiver.Path.nil⟩

instance fundamentalGroupInv (T : RightMeshData Q) (x₀ : Q) :
    Inv (FundamentalGroup T x₀) :=
  ⟨loopInv T x₀⟩

@[simp]
theorem loopClass_mul (T : RightMeshData Q) (x₀ : Q)
    (p q : Walk T x₀ x₀) :
    loopClass T x₀ p * loopClass T x₀ q =
      loopClass T x₀ (p.comp q) :=
  rfl

@[simp]
theorem loopClass_inv (T : RightMeshData Q) (x₀ : Q)
    (p : Walk T x₀ x₀) :
    (loopClass T x₀ p)⁻¹ = loopClass T x₀ (reverseWalk T p) :=
  rfl

@[simp]
theorem loopClass_one (T : RightMeshData Q) (x₀ : Q) :
    loopClass T x₀ Quiver.Path.nil = 1 :=
  rfl

instance fundamentalGroup (T : RightMeshData Q) (x₀ : Q) :
    Group (FundamentalGroup T x₀) where
  mul_assoc a b c := by
    induction a, b, c using Quotient.inductionOn₃ with
    | _ p q r =>
        exact congrArg (loopClass T x₀) (Quiver.Path.comp_assoc p q r)
  one_mul a := by
    induction a using Quotient.inductionOn with
    | _ p => exact congrArg (loopClass T x₀) (Quiver.Path.nil_comp p)
  mul_one a := by
    induction a using Quotient.inductionOn with
    | _ p => exact congrArg (loopClass T x₀) (Quiver.Path.comp_nil p)
  inv_mul_cancel a := by
    induction a using Quotient.inductionOn with
    | _ p =>
        apply Quotient.sound
        change Homotopic T x₀
          ((reverseWalk T p).comp p) Quiver.Path.nil
        simpa only [Quiver.Path.nil_comp] using
          Homotopic.reverse_comp T Quiver.Path.nil p

/-- The universal-cover vertex represented by one augmented walk. -/
def walkVertex (T : RightMeshData Q) (x₀ : Q) {y : Q}
    (p : Walk T x₀ y) : Vertex T x₀ :=
  ⟨y, Quotient.mk _ p⟩

/-- Prepending a fundamental-group loop to a based walk. -/
def deckActVertex (T : RightMeshData Q) (x₀ : Q)
    (g : FundamentalGroup T x₀) (W : Vertex T x₀) : Vertex T x₀ :=
  ⟨W.1, Quotient.map₂ (compWalk T)
    (fun _p p' hp q _q' hq ↦
      Homotopic.trans (Homotopic.comp hp q)
        (Homotopic.left_comp T p' hq)) g W.2⟩

instance fundamentalGroupSMul (T : RightMeshData Q) (x₀ : Q) :
    SMul (FundamentalGroup T x₀) (Vertex T x₀) :=
  ⟨deckActVertex T x₀⟩

@[simp]
theorem loopClass_smul_walkVertex (T : RightMeshData Q) (x₀ : Q)
    (g : Walk T x₀ x₀) {y : Q} (p : Walk T x₀ y) :
    loopClass T x₀ g • walkVertex T x₀ p =
      walkVertex T x₀ (g.comp p) :=
  rfl

@[simp]
theorem deckActVertex_vertex (T : RightMeshData Q) (x₀ : Q)
    (g : FundamentalGroup T x₀) (W : Vertex T x₀) :
    (g • W).1 = W.1 :=
  rfl

instance fundamentalGroupMulAction (T : RightMeshData Q) (x₀ : Q) :
    MulAction (FundamentalGroup T x₀) (Vertex T x₀) where
  one_smul W := by
    rcases W with ⟨y, W⟩
    induction W using Quotient.inductionOn with
    | _ p =>
        change walkVertex T x₀ (Quiver.Path.nil.comp p) =
          walkVertex T x₀ p
        exact congrArg (walkVertex T x₀) (Quiver.Path.nil_comp p)
  mul_smul g h W := by
    rcases W with ⟨y, W⟩
    induction g, h, W using Quotient.inductionOn₃ with
    | _ p q r =>
        change walkVertex T x₀ ((p.comp q).comp r) =
          walkVertex T x₀ (p.comp (q.comp r))
        exact congrArg (walkVertex T x₀) (Quiver.Path.comp_assoc p q r)

/-- Two universal-cover vertices over the same downstairs vertex differ by a
deck transformation. -/
theorem exists_smul_eq_of_vertex_eq (T : RightMeshData Q) (x₀ : Q)
    (W Z : Vertex T x₀) (hvertex : W.1 = Z.1) :
    ∃ g : FundamentalGroup T x₀, g • W = Z := by
  rcases W with ⟨y, W⟩
  rcases Z with ⟨z, Z⟩
  change y = z at hvertex
  subst z
  induction W, Z using Quotient.inductionOn₂ with
  | _ p q =>
      let g := loopClass T x₀ (q.comp (reverseWalk T p))
      refine ⟨g, ?_⟩
      dsimp only [g]
      change
        (⟨y, Quotient.mk (homotopySetoid T x₀ y)
          ((q.comp (reverseWalk T p)).comp p)⟩ : Vertex T x₀) =
        ⟨y, Quotient.mk (homotopySetoid T x₀ y) q⟩
      apply Sigma.ext (by rfl)
      apply heq_of_eq
      apply Quotient.sound
      change Homotopic T x₀
        ((q.comp (reverseWalk T p)).comp p) q
      exact Homotopic.reverse_comp T q p

/-- Deck transformations preserve the downstairs endpoint. -/
theorem vertex_eq_of_smul_eq (T : RightMeshData Q) (x₀ : Q)
    (g : FundamentalGroup T x₀) (W Z : Vertex T x₀)
    (h : g • W = Z) : W.1 = Z.1 := by
  rw [← deckActVertex_vertex T x₀ g W]
  exact congrArg Sigma.fst h

/-- Projection fibres are exactly fundamental-group orbits. -/
theorem vertex_eq_iff_exists_smul_eq (T : RightMeshData Q) (x₀ : Q)
    (W Z : Vertex T x₀) :
    W.1 = Z.1 ↔ ∃ g : FundamentalGroup T x₀, g • W = Z := by
  constructor
  · exact exists_smul_eq_of_vertex_eq T x₀ W Z
  · rintro ⟨g, h⟩
    exact vertex_eq_of_smul_eq T x₀ g W Z h

/-- The deck action is free at every universal-cover vertex. -/
theorem deck_smul_injective (T : RightMeshData Q) (x₀ : Q)
    (W : Vertex T x₀) :
    Function.Injective (fun g : FundamentalGroup T x₀ ↦ g • W) := by
  intro g h hgh
  rcases W with ⟨y, W⟩
  induction g, h, W using Quotient.inductionOn₃ with
  | _ p q r =>
      change walkVertex T x₀ (p.comp r) =
        walkVertex T x₀ (q.comp r) at hgh
      have hquot :
          (Quotient.mk (homotopySetoid T x₀ y) (p.comp r)) =
            Quotient.mk (homotopySetoid T x₀ y) (q.comp r) :=
        eq_of_heq (Sigma.ext_iff.mp hgh).2
      have hrel := Quotient.exact hquot
      change Homotopic T x₀ (p.comp r) (q.comp r) at hrel
      apply Quotient.sound
      change Homotopic T x₀ p q
      exact Homotopic.trans
        (Homotopic.symm (Homotopic.comp_reverse T p r))
        (Homotopic.trans
          (Homotopic.comp hrel (reverseWalk T r))
          (Homotopic.comp_reverse T q r))

instance fundamentalGroupIsCancelSMul (T : RightMeshData Q) (x₀ : Q) :
    IsCancelSMul (FundamentalGroup T x₀) (Vertex T x₀) where
  left_cancel' := IsLeftCancelSMul.left_cancel'
  right_cancel' _g _h W := fun hgh ↦ deck_smul_injective T x₀ W hgh

/-- Deck translation commutes with appending one symmetric augmented arrow. -/
theorem smul_extend (T : RightMeshData Q) (x₀ : Q)
    (g : FundamentalGroup T x₀) (W : Vertex T x₀) {z : Q}
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) W.1 z) :
    g • extend T x₀ W e = extend T x₀ (g • W) e := by
  rcases W with ⟨y, W⟩
  induction g, W using Quotient.inductionOn₂ with
  | _ p q =>
      change
        (⟨z, Quotient.mk (homotopySetoid T x₀ z)
          (p.comp (q.comp e.toPath))⟩ : Vertex T x₀) =
        ⟨z, Quotient.mk (homotopySetoid T x₀ z)
          ((p.comp q).comp e.toPath)⟩
      apply Sigma.ext (by rfl)
      apply heq_of_eq
      exact congrArg (Quotient.mk (homotopySetoid T x₀ z))
        (Quiver.Path.comp_assoc p q e.toPath).symm

/-- Deck translation commutes with lifting one ordinary arrow. -/
theorem smul_extendOld (T : RightMeshData Q) (x₀ : Q)
    (g : FundamentalGroup T x₀) (W : Vertex T x₀) {z : Q}
    (a : W.1 ⟶ z) :
    g • extendOld T x₀ W a = extendOld T x₀ (g • W) a := by
  exact smul_extend T x₀ g W (oldArrow T a)

/-- One deck transformation as an automorphism of the universal-cover
quiver.  It fixes the underlying downstairs arrow. -/
def deckPrefunctor (T : RightMeshData Q) (x₀ : Q)
    (g : FundamentalGroup T x₀) : Prefunctor (Vertex T x₀) (Vertex T x₀) where
  obj := fun W ↦ g • W
  map := fun {W Z} a ↦ ⟨a.1, by
    calc
      extendOld T x₀ (g • W) a.1 =
          g • extendOld T x₀ W a.1 := (smul_extendOld T x₀ g W a.1).symm
      _ = g • Z := congrArg (fun V ↦ g • V) a.2⟩

@[simp]
theorem deckPrefunctor_obj (T : RightMeshData Q) (x₀ : Q)
    (g : FundamentalGroup T x₀) (W : Vertex T x₀) :
    (deckPrefunctor T x₀ g).obj W = g • W :=
  rfl

@[simp]
theorem deckPrefunctor_map_val (T : RightMeshData Q) (x₀ : Q)
    (g : FundamentalGroup T x₀) {W Z : Vertex T x₀} (a : W ⟶ Z) :
    ((deckPrefunctor T x₀ g).map a).1 = a.1 :=
  rfl

/-- The endpoint projection is invariant under every deck transformation. -/
theorem deckPrefunctor_comp_projection (T : RightMeshData Q) (x₀ : Q)
    (g : FundamentalGroup T x₀) :
    (deckPrefunctor T x₀ g).comp (projection T x₀) = projection T x₀ := by
  rfl

/-- Every deck transformation is itself a quiver covering. -/
theorem deckPrefunctor_isCovering (T : RightMeshData Q) (x₀ : Q)
    (g : FundamentalGroup T x₀) :
    (deckPrefunctor T x₀ g).IsCovering := by
  refine Prefunctor.IsCovering.of_comp_right
    (deckPrefunctor T x₀ g) (projection T x₀)
    (projection_isCovering T x₀) ?_
  rw [deckPrefunctor_comp_projection]
  exact projection_isCovering T x₀

set_option backward.isDefEq.respectTransparency false in
/-- A deck transformation commutes with the lifted translation. -/
theorem deckPrefunctor_map_tau (T : RightMeshData Q) (x₀ : Q)
    (g : FundamentalGroup T x₀)
    (W : {W : Vertex T x₀ // W ∉ projectiveSet T x₀}) :
    (deckPrefunctor T x₀ g).obj ((rightMeshData T x₀).tau W) =
      (rightMeshData T x₀).tau
        (mappedNonprojective (rightMeshData T x₀) (rightMeshData T x₀)
          (deckPrefunctor T x₀ g) (fun _ ↦ Iff.rfl) W) := by
  simpa only [rightMeshData, tau, mappedNonprojective,
    baseNonprojective, deckPrefunctor_obj, deckActVertex_vertex] using
    smul_extend T x₀ g W.1
      (meshArrow T (baseNonprojective T x₀ W))

set_option backward.isDefEq.respectTransparency false in
/-- A deck transformation preserves the lifted projective boundary,
translation, and polarization. -/
def deckCover (T : RightMeshData Q) (x₀ : Q)
    (g : FundamentalGroup T x₀) :
    RightMeshData.Cover (rightMeshData T x₀) (rightMeshData T x₀) where
  toPrefunctor := deckPrefunctor T x₀ g
  isCovering := deckPrefunctor_isCovering T x₀ g
  map_projective_iff := fun _ ↦ Iff.rfl
  map_tau := deckPrefunctor_map_tau T x₀ g
  map_arrowEquiv := by
    intro W Y a
    rw [Quiver.Hom.cast_eq_iff_heq]
    rw [Subtype.heq_iff_coe_eq (fun _ ↦ by
      constructor
      · intro h
        exact h.trans (deckPrefunctor_map_tau T x₀ g W)
      · intro h
        exact h.trans (deckPrefunctor_map_tau T x₀ g W).symm)]
    simp only [rightMeshData, arrowEquiv_apply, deckPrefunctor_map_val,
      pairedArrow_val, mappedNonprojective, baseNonprojective,
      deckPrefunctor_obj, deckActVertex_vertex]
    change
      (T.arrowEquiv (baseNonprojective T x₀ W) Y.1) a.1 =
        (T.arrowEquiv (baseNonprojective T x₀ W) Y.1) a.1
    rfl

/-- Every vertex is reachable from the chosen base by an augmented walk.  For
a connected translation quiver this is the based form of connectedness used
by the universal-cover construction. -/
def IsWalkConnectedAt (T : RightMeshData Q) (x₀ : Q) : Prop :=
  ∀ y : Q, Nonempty (Walk T x₀ y)

/-- Under based connectedness, the endpoint projection is surjective on
vertices. -/
theorem vertex_surjective (T : RightMeshData Q) (x₀ : Q)
    (hconnected : IsWalkConnectedAt T x₀) :
    Function.Surjective (vertex T x₀) := by
  intro y
  obtain ⟨p⟩ := hconnected y
  exact ⟨walkVertex T x₀ p, rfl⟩

/-- For a connected base, the orbit set of universal-cover vertices under
the fundamental group is exactly the downstairs vertex set. -/
noncomputable def vertexOrbitEquiv (T : RightMeshData Q) (x₀ : Q)
    (hconnected : IsWalkConnectedAt T x₀) :
    MulAction.orbitRel.Quotient (FundamentalGroup T x₀) (Vertex T x₀) ≃ Q :=
  MagnitudeConjecture.CoveringAction.orbitClassifierEquiv
    (vertex T x₀)
    (fun g W ↦ deckActVertex_vertex T x₀ g W)
    (vertex_surjective T x₀ hconnected)
    (fun X Y hXY ↦ exists_smul_eq_of_vertex_eq T x₀ Y X hXY.symm)

@[simp]
theorem vertexOrbitEquiv_mk (T : RightMeshData Q) (x₀ : Q)
    (hconnected : IsWalkConnectedAt T x₀) (W : Vertex T x₀) :
    vertexOrbitEquiv T x₀ hconnected (Quotient.mk'' W) = W.1 :=
  rfl

universe u

/-- A deck transformation, viewed as a literal endofunctor of the universal
raw mesh category by retaining its ambient source-star finiteness data. -/
def deckMeshEndofunctor (T : RightMeshData Q) (x₀ : Q)
    (g : FundamentalGroup T x₀)
    {k : Type u} [Field k]
    [∀ W : Vertex T x₀, Fintype (Quiver.Star W)] :
    RawCategory (k := k) (rightMeshData T x₀) ⥤
      RawCategory (k := k) (rightMeshData T x₀) :=
  (deckCover T x₀ g).functorUsingSourceFintype (k := k)

noncomputable instance deckMeshEndofunctor_additive
    (T : RightMeshData Q) (x₀ : Q) (g : FundamentalGroup T x₀)
    {k : Type u} [Field k]
    [∀ W : Vertex T x₀, Fintype (Quiver.Star W)] :
    (deckMeshEndofunctor T x₀ g (k := k)).Additive := by
  dsimp only [deckMeshEndofunctor]
  infer_instance

noncomputable instance deckMeshEndofunctor_linear
    (T : RightMeshData Q) (x₀ : Q) (g : FundamentalGroup T x₀)
    {k : Type u} [Field k]
    [∀ W : Vertex T x₀, Fintype (Quiver.Star W)] :
    (deckMeshEndofunctor T x₀ g (k := k)).Linear k := by
  dsimp only [deckMeshEndofunctor]
  infer_instance

@[simp]
theorem deckMeshEndofunctor_obj_obj (T : RightMeshData Q) (x₀ : Q)
    (g : FundamentalGroup T x₀)
    {k : Type u} [Field k]
    [∀ W : Vertex T x₀, Fintype (Quiver.Star W)] (W : Vertex T x₀) :
    (deckMeshEndofunctor T x₀ g (k := k)).obj
        (obj (k := k) (rightMeshData T x₀) W) =
      obj (k := k) (rightMeshData T x₀) (g • W) :=
  rfl

/-- A deck transformation is bijective on the objects of the universal raw
mesh category. -/
theorem deckMeshEndofunctor_obj_bijective (T : RightMeshData Q) (x₀ : Q)
    (g : FundamentalGroup T x₀)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)] :
    let C := cover T x₀
    letI := C.sourceStarFintype
    Function.Bijective ((deckMeshEndofunctor T x₀ g (k := k)).obj) := by
  let C := cover T x₀
  letI := C.sourceStarFintype
  constructor
  · rintro ⟨W⟩ ⟨Z⟩ hWZ
    change
      (deckMeshEndofunctor T x₀ g (k := k)).obj
          (obj (k := k) (rightMeshData T x₀)
            (MagnitudeConjecture.LinearPathCategory.vertex W)) =
        (deckMeshEndofunctor T x₀ g (k := k)).obj
          (obj (k := k) (rightMeshData T x₀)
            (MagnitudeConjecture.LinearPathCategory.vertex Z)) at hWZ
    rw [deckMeshEndofunctor_obj_obj,
      deckMeshEndofunctor_obj_obj] at hWZ
    have haction := congrArg CategoryTheory.Quotient.as hWZ
    change g • MagnitudeConjecture.LinearPathCategory.vertex W =
      g • MagnitudeConjecture.LinearPathCategory.vertex Z at haction
    have hvertex := (MulAction.bijective g).injective haction
    apply CategoryTheory.Quotient.ext
    change MagnitudeConjecture.LinearPathCategory.vertex W =
      MagnitudeConjecture.LinearPathCategory.vertex Z
    exact hvertex
  · rintro ⟨W⟩
    refine ⟨obj (k := k) (rightMeshData T x₀)
      (g⁻¹ • MagnitudeConjecture.LinearPathCategory.vertex W), ?_⟩
    rw [deckMeshEndofunctor_obj_obj]
    apply CategoryTheory.Quotient.ext
    rw [smul_inv_smul]
    rfl

/-- Every literal deck endofunctor is a Bongartz--Gabriel linear covering. -/
theorem deckMeshEndofunctor_isCovering (T : RightMeshData Q) (x₀ : Q)
    (g : FundamentalGroup T x₀)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)] :
    let C := cover T x₀
    letI := C.sourceStarFintype
    MagnitudeConjecture.LinearCovering.IsCovering
      (k := k) (deckMeshEndofunctor T x₀ g (k := k)) := by
  let C := cover T x₀
  letI := C.sourceStarFintype
  exact (deckCover T x₀ g).functorUsingSourceFintype_isCovering (k := k)

/-- Every deck transformation acts by an equivalence of universal raw mesh
categories. -/
theorem deckMeshEndofunctor_isEquivalence (T : RightMeshData Q) (x₀ : Q)
    (g : FundamentalGroup T x₀)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)] :
    let C := cover T x₀
    letI := C.sourceStarFintype
    (deckMeshEndofunctor T x₀ g (k := k)).IsEquivalence := by
  let C := cover T x₀
  letI := C.sourceStarFintype
  exact
    MagnitudeConjecture.LinearCovering.IsCovering.isEquivalenceOfObjBijective
      (deckMeshEndofunctor_isCovering T x₀ g (k := k))
      (deckMeshEndofunctor_obj_bijective T x₀ g (k := k))

/-- The categorical autoequivalence induced by one deck transformation. -/
noncomputable def deckMeshEquivalence (T : RightMeshData Q) (x₀ : Q)
    (g : FundamentalGroup T x₀)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)] :
    let C := cover T x₀
    letI := C.sourceStarFintype
    RawCategory (k := k) (rightMeshData T x₀) ≌
      RawCategory (k := k) (rightMeshData T x₀) := by
  let C := cover T x₀
  letI := C.sourceStarFintype
  let F := deckMeshEndofunctor T x₀ g (k := k)
  letI : F.IsEquivalence :=
    deckMeshEndofunctor_isEquivalence T x₀ g (k := k)
  exact F.asEquivalence

/-- The identity deck transformation acts identically on raw mesh-category
objects. -/
theorem deckMeshEndofunctor_one_obj (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k]
    [∀ W : Vertex T x₀, Fintype (Quiver.Star W)]
    (X : RawCategory (k := k) (rightMeshData T x₀)) :
    (deckMeshEndofunctor T x₀ 1 (k := k)).obj X = X := by
  rcases X with ⟨X⟩
  change
    (deckMeshEndofunctor T x₀ 1 (k := k)).obj
        (obj (k := k) (rightMeshData T x₀)
          (MagnitudeConjecture.LinearPathCategory.vertex X)) =
      obj (k := k) (rightMeshData T x₀)
        (MagnitudeConjecture.LinearPathCategory.vertex X)
  rw [deckMeshEndofunctor_obj_obj]
  apply CategoryTheory.Quotient.ext
  simp

/-- Composition of two deck transformations has the expected left-action
law on raw mesh-category objects. -/
theorem deckMeshEndofunctor_mul_obj (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k]
    [∀ W : Vertex T x₀, Fintype (Quiver.Star W)]
    (g h : FundamentalGroup T x₀)
    (X : RawCategory (k := k) (rightMeshData T x₀)) :
    (deckMeshEndofunctor T x₀ (h * g) (k := k)).obj X =
      (deckMeshEndofunctor T x₀ h (k := k)).obj
        ((deckMeshEndofunctor T x₀ g (k := k)).obj X) := by
  rcases X with ⟨X⟩
  change
    (deckMeshEndofunctor T x₀ (h * g) (k := k)).obj
        (obj (k := k) (rightMeshData T x₀)
          (MagnitudeConjecture.LinearPathCategory.vertex X)) =
      (deckMeshEndofunctor T x₀ h (k := k)).obj
        ((deckMeshEndofunctor T x₀ g (k := k)).obj
          (obj (k := k) (rightMeshData T x₀)
            (MagnitudeConjecture.LinearPathCategory.vertex X)))
  rw [deckMeshEndofunctor_obj_obj,
    deckMeshEndofunctor_obj_obj, deckMeshEndofunctor_obj_obj]
  apply CategoryTheory.Quotient.ext
  change (h * g) • MagnitudeConjecture.LinearPathCategory.vertex X =
    h • g • MagnitudeConjecture.LinearPathCategory.vertex X
  exact mul_smul h g _

set_option backward.isDefEq.respectTransparency false in
/-- The identity deck transformation fixes every universal-cover arrow up
to the dependent endpoint witnesses. -/
theorem deckPrefunctor_one_map_heq (T : RightMeshData Q) (x₀ : Q)
    {W Z : Vertex T x₀} (e : W ⟶ Z) :
    HEq ((deckPrefunctor T x₀ 1).map e) e := by
  rw [Subtype.heq_iff_coe_eq (fun a ↦ by
    constructor
    · intro h
      calc
        extendOld T x₀ W a = 1 • extendOld T x₀ W a :=
          (one_smul (FundamentalGroup T x₀) _).symm
        _ = extendOld T x₀ (1 • W) a := smul_extendOld T x₀ 1 W a
        _ = 1 • Z := h
        _ = Z := one_smul (FundamentalGroup T x₀) Z
    · intro h
      calc
        extendOld T x₀ (1 • W) a = 1 • extendOld T x₀ W a :=
          (smul_extendOld T x₀ 1 W a).symm
        _ = extendOld T x₀ W a := one_smul (FundamentalGroup T x₀) _
        _ = Z := h
        _ = 1 • Z := (one_smul (FundamentalGroup T x₀) Z).symm)]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Mapping a path by the identity deck transformation and then restoring
its endpoints gives the original path. -/
theorem deckPrefunctor_one_mapPath_cast (T : RightMeshData Q) (x₀ : Q)
    {W Z : Vertex T x₀} (p : Quiver.Path W Z) :
    ((deckPrefunctor T x₀ 1).mapPath p).cast
        (one_smul (FundamentalGroup T x₀) W)
        (one_smul (FundamentalGroup T x₀) Z) = p := by
  induction p with
  | nil => simp
  | @cons B Z p e ih =>
      rw [Prefunctor.mapPath_cons, Quiver.Path.cast_cons]
      let hmid := one_smul (FundamentalGroup T x₀) B
      have hpref :
          ((deckPrefunctor T x₀ 1).mapPath p).cast
              (one_smul (FundamentalGroup T x₀) _) rfl =
            p.cast rfl hmid.symm := by
        apply (Quiver.Path.cast_eq_iff_heq _ _ _ _).mpr
        exact HEq.trans
          ((Quiver.Path.cast_eq_iff_heq
            (one_smul (FundamentalGroup T x₀) _) hmid _ _).mp ih)
          (Quiver.Path.cast_heq rfl hmid.symm p).symm
      have harr :
          ((deckPrefunctor T x₀ 1).map e).cast rfl
              (one_smul (FundamentalGroup T x₀) _) =
            e.cast hmid.symm rfl := by
        apply (Quiver.Hom.cast_eq_iff_heq _ _ _ _).mpr
        exact HEq.trans (deckPrefunctor_one_map_heq T x₀ e)
          (Quiver.Hom.cast_heq hmid.symm rfl e).symm
      rw [hpref, harr]
      have internalCast {A B B' C : Vertex T x₀}
          (q : Quiver.Path A B) (a : B ⟶ C) (h : B = B') :
          (q.cast rfl h).cons (a.cast h rfl) = q.cons a := by
        subst B'
        rfl
      exact internalCast p e hmid.symm

/-- Mapping a path by the identity deck transformation changes only its
dependent endpoint witnesses. -/
theorem deckPrefunctor_one_mapPath_heq (T : RightMeshData Q) (x₀ : Q)
    {W Z : Vertex T x₀} (p : Quiver.Path W Z) :
    HEq ((deckPrefunctor T x₀ 1).mapPath p) p :=
  (Quiver.Path.cast_eq_iff_heq
    (one_smul (FundamentalGroup T x₀) W)
    (one_smul (FundamentalGroup T x₀) Z) _ _).mp
      (deckPrefunctor_one_mapPath_cast T x₀ p)

set_option backward.isDefEq.respectTransparency false in
/-- The product deck transformation and the corresponding composite deck
maps agree on arrows up to their dependent endpoint witnesses. -/
theorem deckPrefunctor_mul_map_heq (T : RightMeshData Q) (x₀ : Q)
    (g h : FundamentalGroup T x₀) {W Z : Vertex T x₀} (e : W ⟶ Z) :
    HEq ((deckPrefunctor T x₀ (h * g)).map e)
      ((deckPrefunctor T x₀ h).map
        ((deckPrefunctor T x₀ g).map e)) := by
  rw [Subtype.heq_iff_coe_eq (fun a ↦ by
    constructor
    · intro ha
      calc
        extendOld T x₀ (h • g • W) a =
            h • extendOld T x₀ (g • W) a :=
          (smul_extendOld T x₀ h (g • W) a).symm
        _ = h • (g • extendOld T x₀ W a) :=
          congrArg (fun V ↦ h • V) (smul_extendOld T x₀ g W a).symm
        _ = (h * g) • extendOld T x₀ W a := (mul_smul h g _).symm
        _ = extendOld T x₀ ((h * g) • W) a :=
          smul_extendOld T x₀ (h * g) W a
        _ = (h * g) • Z := ha
        _ = h • g • Z := mul_smul h g Z
    · intro ha
      calc
        extendOld T x₀ ((h * g) • W) a =
            (h * g) • extendOld T x₀ W a :=
          (smul_extendOld T x₀ (h * g) W a).symm
        _ = h • (g • extendOld T x₀ W a) := mul_smul h g _
        _ = h • extendOld T x₀ (g • W) a :=
          congrArg (fun V ↦ h • V) (smul_extendOld T x₀ g W a)
        _ = extendOld T x₀ (h • g • W) a :=
          smul_extendOld T x₀ h (g • W) a
        _ = h • g • Z := ha
        _ = (h * g) • Z := (mul_smul h g Z).symm)]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The product deck map on a path equals successive deck mapping after
restoring the action-law endpoints. -/
theorem deckPrefunctor_mul_mapPath_cast (T : RightMeshData Q) (x₀ : Q)
    (g h : FundamentalGroup T x₀) {W Z : Vertex T x₀}
    (p : Quiver.Path W Z) :
    ((deckPrefunctor T x₀ (h * g)).mapPath p).cast
        (mul_smul h g W) (mul_smul h g Z) =
      (deckPrefunctor T x₀ h).mapPath
        ((deckPrefunctor T x₀ g).mapPath p) := by
  induction p with
  | nil => simp
  | @cons B Z p e ih =>
      rw [Prefunctor.mapPath_cons, Prefunctor.mapPath_cons,
        Prefunctor.mapPath_cons, Quiver.Path.cast_cons]
      let hmid := mul_smul h g B
      have hpref :
          ((deckPrefunctor T x₀ (h * g)).mapPath p).cast
              (mul_smul h g _) rfl =
            ((deckPrefunctor T x₀ h).mapPath
                ((deckPrefunctor T x₀ g).mapPath p)).cast
              rfl hmid.symm := by
        apply (Quiver.Path.cast_eq_iff_heq _ _ _ _).mpr
        exact HEq.trans
          ((Quiver.Path.cast_eq_iff_heq
            (mul_smul h g _) hmid _ _).mp ih)
          (Quiver.Path.cast_heq rfl hmid.symm _).symm
      have harr :
          ((deckPrefunctor T x₀ (h * g)).map e).cast rfl
              (mul_smul h g _) =
            ((deckPrefunctor T x₀ h).map
                ((deckPrefunctor T x₀ g).map e)).cast hmid.symm rfl := by
        apply (Quiver.Hom.cast_eq_iff_heq _ _ _ _).mpr
        exact HEq.trans (deckPrefunctor_mul_map_heq T x₀ g h e)
          (Quiver.Hom.cast_heq hmid.symm rfl _).symm
      rw [hpref, harr]
      have internalCast {A B B' C : Vertex T x₀}
          (q : Quiver.Path A B) (a : B ⟶ C) (hB : B = B') :
          (q.cast rfl hB).cons (a.cast hB rfl) = q.cons a := by
        subst B'
        rfl
      exact internalCast
        ((deckPrefunctor T x₀ h).mapPath
          ((deckPrefunctor T x₀ g).mapPath p))
        ((deckPrefunctor T x₀ h).map
          ((deckPrefunctor T x₀ g).map e)) hmid.symm

/-- Product mapping of a path differs from successive deck mapping only by
dependent endpoint witnesses. -/
theorem deckPrefunctor_mul_mapPath_heq (T : RightMeshData Q) (x₀ : Q)
    (g h : FundamentalGroup T x₀) {W Z : Vertex T x₀}
    (p : Quiver.Path W Z) :
    HEq ((deckPrefunctor T x₀ (h * g)).mapPath p)
      ((deckPrefunctor T x₀ h).mapPath
        ((deckPrefunctor T x₀ g).mapPath p)) :=
  (Quiver.Path.cast_eq_iff_heq (mul_smul h g W) (mul_smul h g Z) _ _).mp
    (deckPrefunctor_mul_mapPath_cast T x₀ g h p)

set_option backward.isDefEq.respectTransparency false in
/-- The objectwise identity comparison for the identity deck
transformation. -/
noncomputable def deckMeshEndofunctorOneIso (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k]
    [∀ W : Vertex T x₀, Fintype (Quiver.Star W)] :
    deckMeshEndofunctor T x₀ 1 (k := k) ≅
      𝟭 (RawCategory (k := k) (rightMeshData T x₀)) :=
  NatIso.ofComponents
    (fun X ↦ eqToIso (deckMeshEndofunctor_one_obj T x₀ (k := k) X))
    (by
      rintro ⟨X⟩ ⟨Y⟩ f
      let Xq : RawCategory (k := k) (rightMeshData T x₀) := ⟨X⟩
      let Yq : RawCategory (k := k) (rightMeshData T x₀) := ⟨Y⟩
      change
        (deckMeshEndofunctor T x₀ 1 (k := k)).map f ≫
            eqToHom (deckMeshEndofunctor_one_obj T x₀ (k := k) Yq) =
          eqToHom (deckMeshEndofunctor_one_obj T x₀ (k := k) Xq) ≫ f
      induction f using Quot.inductionOn with
      | _ f =>
          let lhs : (X ⟶ Y) →ₗ[k]
              ((deckMeshEndofunctor T x₀ 1 (k := k)).obj Xq ⟶ Yq) :=
            { toFun := fun a ↦
                (deckMeshEndofunctor T x₀ 1 (k := k)).map
                    ((quotientFunctor (k := k) (rightMeshData T x₀)).map a) ≫
                  eqToHom (deckMeshEndofunctor_one_obj T x₀ (k := k) Yq)
              map_add' := by
                intro a b
                rw [(quotientFunctor (k := k)
                    (rightMeshData T x₀)).map_add,
                  (deckMeshEndofunctor T x₀ 1 (k := k)).map_add,
                  Preadditive.add_comp]
              map_smul' := by
                intro r a
                rw [(quotientFunctor (k := k)
                    (rightMeshData T x₀)).map_smul,
                  (deckMeshEndofunctor T x₀ 1 (k := k)).map_smul,
                  CategoryTheory.Linear.smul_comp]
                simp only [RingHom.id_apply] }
          let rhs : (X ⟶ Y) →ₗ[k]
              ((deckMeshEndofunctor T x₀ 1 (k := k)).obj Xq ⟶ Yq) :=
            { toFun := fun a ↦
                eqToHom (deckMeshEndofunctor_one_obj T x₀ (k := k) Xq) ≫
                  (quotientFunctor (k := k) (rightMeshData T x₀)).map a
              map_add' := by
                intro a b
                rw [(quotientFunctor (k := k)
                    (rightMeshData T x₀)).map_add,
                  Preadditive.comp_add]
              map_smul' := by
                intro r a
                rw [(quotientFunctor (k := k)
                    (rightMeshData T x₀)).map_smul,
                  CategoryTheory.Linear.comp_smul]
                simp only [RingHom.id_apply] }
          change lhs f = rhs f
          have hlr : lhs = rhs := by
            apply (MagnitudeConjecture.LinearPathCategory.homPathBasis
              X Y).ext
            intro p
            dsimp only [lhs, rhs]
            simp only [MagnitudeConjecture.LinearPathCategory.homPathBasis_apply]
            change
              (deckMeshEndofunctor T x₀ 1 (k := k)).map
                    ((quotientFunctor (k := k) (rightMeshData T x₀)).map
                      (MagnitudeConjecture.LinearPathCategory.pathHom p)) ≫
                  eqToHom (deckMeshEndofunctor_one_obj T x₀ (k := k) Yq) =
                eqToHom (deckMeshEndofunctor_one_obj T x₀ (k := k) Xq) ≫
                  (quotientFunctor (k := k) (rightMeshData T x₀)).map
                    (MagnitudeConjecture.LinearPathCategory.pathHom p)
            unfold deckMeshEndofunctor
            rw [(deckCover T x₀ 1).functorUsingSourceFintype_map_quotient_pathHom]
            let q := quotientFunctor (k := k) (rightMeshData T x₀)
            let hY := one_smul (FundamentalGroup T x₀)
              (MagnitudeConjecture.LinearPathCategory.vertex Y)
            let hX := one_smul (FundamentalGroup T x₀)
              (MagnitudeConjecture.LinearPathCategory.vertex X)
            let hYfree := congrArg
              (MagnitudeConjecture.LinearPathCategory.obj k (Vertex T x₀)) hY
            let hXfree := congrArg
              (MagnitudeConjecture.LinearPathCategory.obj k (Vertex T x₀)) hX
            have hYraw :
                deckMeshEndofunctor_one_obj T x₀ (k := k) Yq =
                  congrArg q.obj hYfree := Subsingleton.elim _ _
            have hXraw :
                deckMeshEndofunctor_one_obj T x₀ (k := k) Xq =
                  congrArg q.obj hXfree := Subsingleton.elim _ _
            rw [hYraw, hXraw, ← eqToHom_map q hYfree,
              ← eqToHom_map q hXfree, ← q.map_comp, ← q.map_comp]
            apply congrArg q.map
            change
              MagnitudeConjecture.LinearPathCategory.pathHom
                    ((deckPrefunctor T x₀ 1).mapPath p) ≫
                  eqToHom hYfree =
                eqToHom hXfree ≫
                  MagnitudeConjecture.LinearPathCategory.pathHom p
            rw [MagnitudeConjecture.LinearPathCategory.pathHom_comp_eqToHom_eq_cast_start
                (k := k)
                ((deckPrefunctor T x₀ 1).mapPath p) hY,
              MagnitudeConjecture.LinearPathCategory.eqToHom_comp_pathHom_eq_cast_end
                (k := k) p hX.symm]
            apply congrArg MagnitudeConjecture.LinearPathCategory.pathHom
            apply eq_of_heq
            exact HEq.trans
              (Quiver.Path.cast_heq hY rfl
                ((deckPrefunctor T x₀ 1).mapPath p))
              (HEq.trans (deckPrefunctor_one_mapPath_heq T x₀ p)
                (Quiver.Path.cast_heq rfl hX.symm p).symm)
          rw [hlr])

set_option backward.isDefEq.respectTransparency false in
/-- The natural product comparison for categorical deck transformations.
The order is the left-action order: first `g`, then `h`, equals `h * g`. -/
noncomputable def deckMeshEndofunctorMulIso (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k]
    [∀ W : Vertex T x₀, Fintype (Quiver.Star W)]
    (g h : FundamentalGroup T x₀) :
    deckMeshEndofunctor T x₀ (h * g) (k := k) ≅
      deckMeshEndofunctor T x₀ g (k := k) ⋙
        deckMeshEndofunctor T x₀ h (k := k) :=
  NatIso.ofComponents
    (fun X ↦ eqToIso (deckMeshEndofunctor_mul_obj T x₀ (k := k) g h X))
    (by
      rintro ⟨X⟩ ⟨Y⟩ f
      let Xq : RawCategory (k := k) (rightMeshData T x₀) := ⟨X⟩
      let Yq : RawCategory (k := k) (rightMeshData T x₀) := ⟨Y⟩
      change
        (deckMeshEndofunctor T x₀ (h * g) (k := k)).map f ≫
            eqToHom (deckMeshEndofunctor_mul_obj T x₀ (k := k) g h Yq) =
          eqToHom (deckMeshEndofunctor_mul_obj T x₀ (k := k) g h Xq) ≫
            (deckMeshEndofunctor T x₀ h (k := k)).map
              ((deckMeshEndofunctor T x₀ g (k := k)).map f)
      induction f using Quot.inductionOn with
      | _ f =>
          let lhs : (X ⟶ Y) →ₗ[k]
              ((deckMeshEndofunctor T x₀ (h * g) (k := k)).obj Xq ⟶
                (deckMeshEndofunctor T x₀ h (k := k)).obj
                  ((deckMeshEndofunctor T x₀ g (k := k)).obj Yq)) :=
            { toFun := fun a ↦
                (deckMeshEndofunctor T x₀ (h * g) (k := k)).map
                    ((quotientFunctor (k := k) (rightMeshData T x₀)).map a) ≫
                  eqToHom
                    (deckMeshEndofunctor_mul_obj T x₀ (k := k) g h Yq)
              map_add' := by
                intro a b
                rw [(quotientFunctor (k := k)
                    (rightMeshData T x₀)).map_add,
                  (deckMeshEndofunctor T x₀ (h * g) (k := k)).map_add,
                  Preadditive.add_comp]
              map_smul' := by
                intro r a
                rw [(quotientFunctor (k := k)
                    (rightMeshData T x₀)).map_smul,
                  (deckMeshEndofunctor T x₀ (h * g) (k := k)).map_smul,
                  CategoryTheory.Linear.smul_comp]
                simp only [RingHom.id_apply] }
          let rhs : (X ⟶ Y) →ₗ[k]
              ((deckMeshEndofunctor T x₀ (h * g) (k := k)).obj Xq ⟶
                (deckMeshEndofunctor T x₀ h (k := k)).obj
                  ((deckMeshEndofunctor T x₀ g (k := k)).obj Yq)) :=
            { toFun := fun a ↦
                eqToHom
                    (deckMeshEndofunctor_mul_obj T x₀ (k := k) g h Xq) ≫
                  (deckMeshEndofunctor T x₀ h (k := k)).map
                    ((deckMeshEndofunctor T x₀ g (k := k)).map
                      ((quotientFunctor (k := k)
                        (rightMeshData T x₀)).map a))
              map_add' := by
                intro a b
                rw [(quotientFunctor (k := k)
                    (rightMeshData T x₀)).map_add,
                  (deckMeshEndofunctor T x₀ g (k := k)).map_add,
                  (deckMeshEndofunctor T x₀ h (k := k)).map_add,
                  Preadditive.comp_add]
              map_smul' := by
                intro r a
                rw [(quotientFunctor (k := k)
                    (rightMeshData T x₀)).map_smul,
                  (deckMeshEndofunctor T x₀ g (k := k)).map_smul,
                  (deckMeshEndofunctor T x₀ h (k := k)).map_smul,
                  CategoryTheory.Linear.comp_smul]
                simp only [RingHom.id_apply] }
          change lhs f = rhs f
          have hlr : lhs = rhs := by
            apply (MagnitudeConjecture.LinearPathCategory.homPathBasis X Y).ext
            intro p
            dsimp only [lhs, rhs]
            simp only [MagnitudeConjecture.LinearPathCategory.homPathBasis_apply]
            change
              (deckMeshEndofunctor T x₀ (h * g) (k := k)).map
                    ((quotientFunctor (k := k) (rightMeshData T x₀)).map
                      (MagnitudeConjecture.LinearPathCategory.pathHom p)) ≫
                  eqToHom
                    (deckMeshEndofunctor_mul_obj T x₀ (k := k) g h Yq) =
                eqToHom
                    (deckMeshEndofunctor_mul_obj T x₀ (k := k) g h Xq) ≫
                  (deckMeshEndofunctor T x₀ h (k := k)).map
                    ((deckMeshEndofunctor T x₀ g (k := k)).map
                      ((quotientFunctor (k := k)
                        (rightMeshData T x₀)).map
                          (MagnitudeConjecture.LinearPathCategory.pathHom p)))
            unfold deckMeshEndofunctor
            rw [(deckCover T x₀ (h * g)).functorUsingSourceFintype_map_quotient_pathHom,
              (deckCover T x₀ g).functorUsingSourceFintype_map_quotient_pathHom,
              (deckCover T x₀ h).functorUsingSourceFintype_map_quotient_pathHom]
            let q := quotientFunctor (k := k) (rightMeshData T x₀)
            let hY := mul_smul h g
              (MagnitudeConjecture.LinearPathCategory.vertex Y)
            let hX := mul_smul h g
              (MagnitudeConjecture.LinearPathCategory.vertex X)
            let hYfree := congrArg
              (MagnitudeConjecture.LinearPathCategory.obj k (Vertex T x₀)) hY
            let hXfree := congrArg
              (MagnitudeConjecture.LinearPathCategory.obj k (Vertex T x₀)) hX
            have hYraw :
                deckMeshEndofunctor_mul_obj T x₀ (k := k) g h Yq =
                  congrArg q.obj hYfree := Subsingleton.elim _ _
            have hXraw :
                deckMeshEndofunctor_mul_obj T x₀ (k := k) g h Xq =
                  congrArg q.obj hXfree := Subsingleton.elim _ _
            rw [hYraw, hXraw, ← eqToHom_map q hYfree,
              ← eqToHom_map q hXfree, ← q.map_comp, ← q.map_comp]
            apply congrArg q.map
            change
              MagnitudeConjecture.LinearPathCategory.pathHom
                    ((deckPrefunctor T x₀ (h * g)).mapPath p) ≫
                  eqToHom hYfree =
                eqToHom hXfree ≫
                  MagnitudeConjecture.LinearPathCategory.pathHom
                    ((deckPrefunctor T x₀ h).mapPath
                      ((deckPrefunctor T x₀ g).mapPath p))
            rw [MagnitudeConjecture.LinearPathCategory.pathHom_comp_eqToHom_eq_cast_start
                (k := k)
                ((deckPrefunctor T x₀ (h * g)).mapPath p) hY,
              MagnitudeConjecture.LinearPathCategory.eqToHom_comp_pathHom_eq_cast_end
                (k := k)
                ((deckPrefunctor T x₀ h).mapPath
                  ((deckPrefunctor T x₀ g).mapPath p)) hX.symm]
            apply congrArg MagnitudeConjecture.LinearPathCategory.pathHom
            apply eq_of_heq
            exact HEq.trans
              (Quiver.Path.cast_heq hY rfl
                ((deckPrefunctor T x₀ (h * g)).mapPath p))
              (HEq.trans (deckPrefunctor_mul_mapPath_heq T x₀ g h p)
                (Quiver.Path.cast_heq rfl hX.symm
                  ((deckPrefunctor T x₀ h).mapPath
                  ((deckPrefunctor T x₀ g).mapPath p))).symm)
          rw [hlr])

/-- The fundamental group acts on the objects of the universal raw mesh
category through the already constructed vertex action. -/
def rawMeshDeckSMul (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k]
    [∀ W : Vertex T x₀, Fintype (Quiver.Star W)]
    (g : FundamentalGroup T x₀)
    (X : RawCategory (k := k) (rightMeshData T x₀)) :
    RawCategory (k := k) (rightMeshData T x₀) :=
  obj (k := k) (rightMeshData T x₀)
    (g • MagnitudeConjecture.LinearPathCategory.vertex X.as)

instance rawMeshDeckMulAction (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k]
    [∀ W : Vertex T x₀, Fintype (Quiver.Star W)] :
    MulAction (FundamentalGroup T x₀)
      (RawCategory (k := k) (rightMeshData T x₀)) where
  smul := rawMeshDeckSMul T x₀
  one_smul X := by
    rcases X with ⟨X⟩
    apply CategoryTheory.Quotient.ext
    change 1 • MagnitudeConjecture.LinearPathCategory.vertex X =
      MagnitudeConjecture.LinearPathCategory.vertex X
    simp
  mul_smul g h X := by
    rcases X with ⟨X⟩
    apply CategoryTheory.Quotient.ext
    change (g * h) • MagnitudeConjecture.LinearPathCategory.vertex X =
      g • h • MagnitudeConjecture.LinearPathCategory.vertex X
    exact mul_smul g h _

instance rawMeshDeckIsCancelSMul (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k]
    [∀ W : Vertex T x₀, Fintype (Quiver.Star W)] :
    IsCancelSMul (FundamentalGroup T x₀)
      (RawCategory (k := k) (rightMeshData T x₀)) where
  left_cancel' := IsLeftCancelSMul.left_cancel'
  right_cancel' g h X hgh := by
    rcases X with ⟨X⟩
    apply deck_smul_injective T x₀
      (MagnitudeConjecture.LinearPathCategory.vertex X)
    have heq := congrArg CategoryTheory.Quotient.as hgh
    change g • MagnitudeConjecture.LinearPathCategory.vertex X =
      h • MagnitudeConjecture.LinearPathCategory.vertex X at heq
    exact heq

/-- The categorical deck endofunctor has exactly the induced deck action as
its object map. -/
theorem deckMeshEndofunctor_obj_eq_smul (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k]
    [∀ W : Vertex T x₀, Fintype (Quiver.Star W)]
    (g : FundamentalGroup T x₀)
    (X : RawCategory (k := k) (rightMeshData T x₀)) :
    (deckMeshEndofunctor T x₀ g (k := k)).obj X = g • X := by
  rcases X with ⟨X⟩
  change
    (deckMeshEndofunctor T x₀ g (k := k)).obj
        (obj (k := k) (rightMeshData T x₀)
          (MagnitudeConjecture.LinearPathCategory.vertex X)) = _
  rw [deckMeshEndofunctor_obj_obj]
  rfl

/-- Multiplication written through the additive type synonym, with an
explicit equality proof suitable for dependent coherence calculations. -/
theorem additiveToMul_add {G : Type*} [Mul G] (a b : Additive G) :
    (a + b).toMul = a.toMul * b.toMul :=
  rfl

/-- The coherent right-shift core obtained from the left fundamental-group
action.  Additive degree `g` is the inverse deck transformation `g⁻¹`. -/
noncomputable def deckMeshShiftCore (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k]
    [∀ W : Vertex T x₀, Fintype (Quiver.Star W)] :
    ShiftMkCore (RawCategory (k := k) (rightMeshData T x₀))
      (Additive (FundamentalGroup T x₀)) where
  F a := deckMeshEndofunctor T x₀ a.toMul⁻¹ (k := k)
  zero := by
    let e : (0 : Additive (FundamentalGroup T x₀)).toMul⁻¹ = 1 := by simp
    exact eqToIso (congrArg
      (fun g ↦ deckMeshEndofunctor T x₀ g (k := k)) e) ≪≫
        deckMeshEndofunctorOneIso T x₀ (k := k)
  add a b := by
    let e : (a + b).toMul⁻¹ = b.toMul⁻¹ * a.toMul⁻¹ :=
      (congrArg (fun g ↦ g⁻¹) (additiveToMul_add a b)).trans
        (mul_inv_rev a.toMul b.toMul)
    exact eqToIso (congrArg
      (fun g ↦ deckMeshEndofunctor T x₀ g (k := k)) e) ≪≫
        deckMeshEndofunctorMulIso T x₀ (k := k) a.toMul⁻¹ b.toMul⁻¹
  assoc_hom_app := by
    intro a b c X
    simp [deckMeshEndofunctorMulIso]
    rw [eqToHom_map]
    apply eq_of_heq
    exact HEq.trans
      (HEq.trans (comp_eqToHom_heq _ _)
        (eqToHom_heq_id_dom _ _ _))
      (eqToHom_heq_id_dom _ _ _).symm
  zero_add_hom_app := by
    intro a X
    simp [deckMeshEndofunctorMulIso, deckMeshEndofunctorOneIso]
    rw [eqToHom_map]
    apply eq_of_heq
    exact HEq.trans (eqToHom_heq_id_dom _ _ _)
      (HEq.trans (comp_eqToHom_heq _ _)
        (eqToHom_heq_id_dom _ _ _)).symm
  add_zero_hom_app := by
    intro a X
    simp [deckMeshEndofunctorMulIso, deckMeshEndofunctorOneIso]

noncomputable instance deckMeshShiftCore_additive
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k]
    [∀ W : Vertex T x₀, Fintype (Quiver.Star W)]
    (a : Additive (FundamentalGroup T x₀)) :
    ((deckMeshShiftCore T x₀ (k := k)).F a).Additive := by
  change (deckMeshEndofunctor T x₀ a.toMul⁻¹ (k := k)).Additive
  infer_instance

noncomputable instance deckMeshShiftCore_linear
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k]
    [∀ W : Vertex T x₀, Fintype (Quiver.Star W)]
    (a : Additive (FundamentalGroup T x₀)) :
    ((deckMeshShiftCore T x₀ (k := k)).F a).Linear k := by
  change (deckMeshEndofunctor T x₀ a.toMul⁻¹ (k := k)).Linear k
  infer_instance

/-- The universal raw mesh category equipped with its coherent
fundamental-group deck shifts. -/
noncomputable def deckMeshCoherentDeckShift (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k]
    [∀ W : Vertex T x₀, Fintype (Quiver.Star W)] :
    MagnitudeConjecture.CoveringHom.CoherentDeckShift
      (RawCategory (k := k) (rightMeshData T x₀))
      (FundamentalGroup T x₀) where
  core := deckMeshShiftCore T x₀ (k := k)
  objIso g X := eqToIso
    (deckMeshEndofunctor_obj_eq_smul T x₀ (k := k) g⁻¹ X)

end MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover
