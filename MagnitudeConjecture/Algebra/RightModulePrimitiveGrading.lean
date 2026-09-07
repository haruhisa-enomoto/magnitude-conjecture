import MagnitudeConjecture.Algebra.RightModulePrimitivePosetEquivalence
import MagnitudeConjecture.CategoryTheory.RepresentableGrading

/-!
# The grading interface on the primitive factor skeleton

The representation-directed standardness step in the frozen manuscript gives
the surviving indecomposable skeleton a positive path-length grading.  This
file records the exact output needed by the poset-space argument and proves
all subsequent concentration statements from it.

The chosen maps `P ⟶ P_t` need not be included as extra homogeneous data:
their Hom spaces are one-dimensional, so internal direct-sum uniqueness makes
each chosen nonzero map homogeneous in a unique degree.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}
variable {T : Type u} [Fintype T] [PartialOrder T]

/-- A positive internal grading on the Hom spaces between surviving selected
indecomposables.  Composition adds degrees, and distinct skeleton objects
have no degree-zero morphisms. -/
structure SkeletonHomGrading
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (K : Set (Fin S.n)) where
  component : ∀ x y : S.SurvivingLabel K, ℕ →
    Submodule k (S.factorObject K x ⟶ S.factorObject K y)
  isInternal : ∀ x y, DirectSum.IsInternal (component x y)
  comp_mem : ∀ {x y z : S.SurvivingLabel K} {i j : ℕ}
    {f : S.factorObject K x ⟶ S.factorObject K y}
    {g : S.factorObject K y ⟶ S.factorObject K z},
    f ∈ component x y i → g ∈ component y z j →
      f ≫ g ∈ component x z (i + j)
  id_mem_zero : ∀ x : S.SurvivingLabel K,
    𝟙 (S.factorObject K x) ∈ component x x 0
  degreeZero_eq_bot_of_ne : ∀ {x y : S.SurvivingLabel K}, x ≠ y →
    component x y 0 = ⊥

namespace SkeletonHomGrading

variable {R : S.PrimitiveProjectivePosetData D T}

/-- The represented Hom space `Hom(P,P_t)` is one-dimensional. -/
theorem source_projective_finrank_eq_one
    (R : S.PrimitiveProjectivePosetData D T) (t : T) :
    Module.finrank k
      (S.factorObject K D.source ⟶ S.factorObject K (R.label t)) = 1 := by
  exact
    (PrimitiveMultiplicityInput.factorHomFrom_finrank_eq_multiplicity
      (S := S) D (R.label t)).trans
      (R.projective_multiplicity_eq_one
        (R.projectiveEquiv.symm (some t)))

/-- The unique homogeneous degree of the chosen nonzero map `P ⟶ P_t`. -/
noncomputable def unitDegree (G : S.SkeletonHomGrading K)
    (R : S.PrimitiveProjectivePosetData D T) (t : T) : ℕ :=
  (GradedLinear.existsUnique_mem_of_finrank_eq_one
    (G.component D.source (R.label t))
    (G.isInternal D.source (R.label t))
    (source_projective_finrank_eq_one R t) (R.unit_ne_zero t)).choose

theorem unit_mem (G : S.SkeletonHomGrading K)
    (R : S.PrimitiveProjectivePosetData D T) (t : T) :
    R.unit t ∈ G.component D.source (R.label t) (G.unitDegree R t) :=
    (GradedLinear.existsUnique_mem_of_finrank_eq_one
    (G.component D.source (R.label t))
    (G.isInternal D.source (R.label t))
    (source_projective_finrank_eq_one R t) (R.unit_ne_zero t)).choose_spec.1

/-- Precomposition by the chosen map `P ⟶ P_t` shifts the skeleton grading
by the uniquely determined degree of that map. -/
theorem precomposition_shiftsDegree (G : S.SkeletonHomGrading K)
    (R : S.PrimitiveProjectivePosetData D T)
    (t : T) (x : S.SurvivingLabel K) :
    GradedLinear.ShiftsDegree
      (G.component (R.label t) x)
      (G.component D.source x)
      (R.representableData.precomposition t (S.factorObject K x))
      (G.unitDegree R t) := by
  intro i f hf
  change R.unit t ≫ f ∈
    G.component D.source x (i + G.unitDegree R t)
  simpa [Nat.add_comm] using G.comp_mem (G.unit_mem R t) hf

/-- The represented poset space of a surviving indecomposable inherits the
internal grading on `Hom(P,X)`. -/
def objInternalGrading (G : S.SkeletonHomGrading K)
    (R : S.PrimitiveProjectivePosetData D T)
    (x : S.SurvivingLabel K) :
    PosetSpace.InternalGrading
      (R.representableData.obj (S.factorObject K x)) where
  component := G.component D.source x
  isInternal := G.isInternal D.source x
  subspace_isHomogeneous := by
    letI : DirectSum.Decomposition (G.component D.source x) :=
      (G.isInternal D.source x).chooseDecomposition
    intro t
    change DirectSum.SetLike.IsHomogeneous
      (G.component D.source x)
      (LinearMap.range
        (R.representableData.precomposition t (S.factorObject K x)))
    exact GradedLinear.ShiftsDegree.range_isHomogeneous
      (G.component (R.label t) x) (G.component D.source x)
      (G.isInternal (R.label t) x) (G.isInternal D.source x)
      (R.representableData.precomposition t (S.factorObject K x))
      (G.precomposition_shiftsDegree R t x)

/-- A homogeneous factor morphism induces a homogeneous map of represented
poset spaces of the same degree. -/
theorem map_homogeneousOfDegree (G : S.SkeletonHomGrading K)
    (R : S.PrimitiveProjectivePosetData D T)
    {x y : S.SurvivingLabel K}
    {f : S.factorObject K x ⟶ S.factorObject K y} {d : ℕ}
    (hf : f ∈ G.component x y d) :
    PosetSpace.InternalGrading.HomogeneousOfDegree
      (G.objInternalGrading R x) (G.objInternalGrading R y)
      (R.representableData.map f) d := by
  intro i h hi
  exact G.comp_mem hi hf

/-- The concentration level of a surviving indecomposable under the
completed primitive poset-space realization. -/
noncomputable def objLevel [IsAlgClosed k]
    (G : S.SkeletonHomGrading K)
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (hsink : D.multiplicity D.sink.1 = 1)
    (x : S.SurvivingLabel K) : ℕ :=
  (G.objInternalGrading R x).level
    ((R.schurRealizationFamily H hsink).schur x)

@[simp]
theorem obj_component_level_eq_top [IsAlgClosed k]
    (G : S.SkeletonHomGrading K)
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (hsink : D.multiplicity D.sink.1 = 1)
    (x : S.SurvivingLabel K) :
    G.component D.source x (G.objLevel R H hsink x) = ⊤ :=
  (G.objInternalGrading R x).component_level_eq_top
    ((R.schurRealizationFamily H hsink).schur x)

/-- The primitive source is concentrated in degree zero. -/
theorem objLevel_source_eq_zero [IsAlgClosed k]
    (G : S.SkeletonHomGrading K)
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (hsink : D.multiplicity D.sink.1 = 1) :
    G.objLevel R H hsink D.source = 0 := by
  let hsource := (R.schurRealizationFamily H hsink).schur D.source
  have hne : G.component D.source D.source 0 ≠ ⊥ := by
    intro hbot
    have hidzero :
        (𝟙 (S.factorObject K D.source) :
          S.factorObject K D.source ⟶ S.factorObject K D.source) = 0 := by
      have : (𝟙 (S.factorObject K D.source) :
          S.factorObject K D.source ⟶ S.factorObject K D.source) ∈
          (⊥ : Submodule k
            (S.factorObject K D.source ⟶ S.factorObject K D.source)) :=
        hbot ▸ G.id_mem_zero D.source
      simpa using this
    exact S.factorObject_not_isZero K D.source
      ((IsZero.iff_id_eq_zero _).2 hidzero)
  exact ((G.objInternalGrading R D.source).eq_level_of_component_eq_top hsource
    ((G.objInternalGrading R D.source).component_eq_top_of_ne_bot_of_isSchur
      hsource 0 hne)).symm

/-- A nonzero homogeneous factor morphism raises concentration level by
exactly its homogeneous degree. -/
theorem objLevel_add_degree_eq_of_mem [IsAlgClosed k]
    (G : S.SkeletonHomGrading K)
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (hsink : D.multiplicity D.sink.1 = 1)
    {x y : S.SurvivingLabel K}
    {f : S.factorObject K x ⟶ S.factorObject K y} {d : ℕ}
    (hf : f ≠ 0) (hfd : f ∈ G.component x y d) :
    G.objLevel R H hsink x + d = G.objLevel R H hsink y := by
  let hX := (R.schurRealizationFamily H hsink).schur x
  let hY := (R.schurRealizationFamily H hsink).schur y
  apply PosetSpace.InternalGrading.level_add_degree_eq
    (G.objInternalGrading R x) (G.objInternalGrading R y) hX hY
  · intro hmap
    apply hf
    apply R.representable_faithful.map_injective
    calc
      R.representableData.map f = 0 := hmap
      _ = R.representableData.map 0 := by
        apply PosetSpace.Hom.ext
        apply LinearMap.ext
        intro h
        change 0 = h ≫ (0 : S.factorObject K x ⟶ S.factorObject K y)
        simp
  · exact G.map_homogeneousOfDegree R hfd

/-- The degree-`d` homogeneous component of a factor morphism. -/
noncomputable def homogeneousComponent (G : S.SkeletonHomGrading K)
    {x y : S.SurvivingLabel K}
    (f : S.factorObject K x ⟶ S.factorObject K y) (d : ℕ) :
    S.factorObject K x ⟶ S.factorObject K y := by
  letI : DirectSum.Decomposition (G.component x y) :=
    (G.isInternal x y).chooseDecomposition
  exact ((DirectSum.decompose (G.component x y) f d :
    G.component x y d) : S.factorObject K x ⟶ S.factorObject K y)

theorem homogeneousComponent_mem (G : S.SkeletonHomGrading K)
    {x y : S.SurvivingLabel K}
    (f : S.factorObject K x ⟶ S.factorObject K y) (d : ℕ) :
    G.homogeneousComponent f d ∈ G.component x y d := by
  letI : DirectSum.Decomposition (G.component x y) :=
    (G.isInternal x y).chooseDecomposition
  change ((DirectSum.decompose (G.component x y) f d :
    G.component x y d) : S.factorObject K x ⟶ S.factorObject K y) ∈
      G.component x y d
  exact (DirectSum.decompose (G.component x y) f d).property

theorem exists_homogeneousComponent_ne_zero (G : S.SkeletonHomGrading K)
    {x y : S.SurvivingLabel K}
    {f : S.factorObject K x ⟶ S.factorObject K y} (hf : f ≠ 0) :
    ∃ d, G.homogeneousComponent f d ≠ 0 := by
  classical
  letI : DirectSum.Decomposition (G.component x y) :=
    (G.isInternal x y).chooseDecomposition
  by_contra h
  push Not at h
  apply hf
  rw [← DirectSum.sum_support_decompose (G.component x y) f]
  apply Finset.sum_eq_zero
  intro d hd
  simpa [homogeneousComponent] using h d

/-- Every nonzero factor morphism is homogeneous in one degree, and that
degree is the difference of the concentration levels of its endpoints. -/
theorem exists_degree_mem_and_objLevel_eq [IsAlgClosed k]
    (G : S.SkeletonHomGrading K)
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (hsink : D.multiplicity D.sink.1 = 1)
    {x y : S.SurvivingLabel K}
    {f : S.factorObject K x ⟶ S.factorObject K y} (hf : f ≠ 0) :
    ∃ d, f ∈ G.component x y d ∧
      G.objLevel R H hsink x + d = G.objLevel R H hsink y := by
  classical
  letI : DirectSum.Decomposition (G.component x y) :=
    (G.isInternal x y).chooseDecomposition
  obtain ⟨d, hd⟩ := G.exists_homogeneousComponent_ne_zero hf
  have hdmem := G.homogeneousComponent_mem f d
  have hdlevel := G.objLevel_add_degree_eq_of_mem R H hsink hd hdmem
  refine ⟨d, ?_, hdlevel⟩
  rw [← DirectSum.sum_support_decompose (G.component x y) f]
  apply Submodule.sum_mem
  intro e he
  by_cases hed : e = d
  · subst e
    exact (DirectSum.decompose (G.component x y) f d).property
  · have hezero : G.homogeneousComponent f e = 0 := by
      by_contra hene
      have helevel := G.objLevel_add_degree_eq_of_mem R H hsink hene
        (G.homogeneousComponent_mem f e)
      exact hed (Nat.add_left_cancel (helevel.trans hdlevel.symm))
    have hezero' :
        ((DirectSum.decompose (G.component x y) f e :
          G.component x y e) :
            S.factorObject K x ⟶ S.factorObject K y) = 0 := by
      simpa [homogeneousComponent] using hezero
    rw [hezero']
    exact Submodule.zero_mem _

/-- The homogeneous degree of a nonzero factor morphism is unique. -/
theorem existsUnique_degree_mem [IsAlgClosed k]
    (G : S.SkeletonHomGrading K)
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (hsink : D.multiplicity D.sink.1 = 1)
    {x y : S.SurvivingLabel K}
    {f : S.factorObject K x ⟶ S.factorObject K y} (hf : f ≠ 0) :
    ∃! d, f ∈ G.component x y d := by
  obtain ⟨d, hfd, hdlevel⟩ :=
    G.exists_degree_mem_and_objLevel_eq R H hsink hf
  refine ⟨d, hfd, ?_⟩
  intro e hfe
  exact Nat.add_left_cancel
    ((G.objLevel_add_degree_eq_of_mem R H hsink hf hfe).trans hdlevel.symm)

/-- A nonzero nonisomorphism between surviving indecomposables strictly
raises the concentration level. -/
theorem objLevel_lt_of_nonzero_not_isIso [IsAlgClosed k]
    (G : S.SkeletonHomGrading K)
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (hsink : D.multiplicity D.sink.1 = 1)
    {x y : S.SurvivingLabel K}
    (f : S.factorObject K x ⟶ S.factorObject K y)
    (hf : f ≠ 0) (hniso : ¬ IsIso f) :
    G.objLevel R H hsink x < G.objLevel R H hsink y := by
  have hxy : x ≠ y := by
    intro hxy
    subst y
    obtain ⟨c, hc⟩ := H.factorObject_endomorphism_eq_smul_id S K x f
    have hc0 : c ≠ 0 := by
      intro hczero
      apply hf
      rw [← hc, hczero, zero_smul]
    apply hniso
    rw [← hc]
    exact ⟨⟨c⁻¹ • 𝟙 (S.factorObject K x), by simp [hc0], by simp [hc0]⟩⟩
  obtain ⟨d, hfd, hdlevel⟩ :=
    G.exists_degree_mem_and_objLevel_eq R H hsink hf
  have hdpos : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hd0
    subst d
    rw [G.degreeZero_eq_bot_of_ne hxy] at hfd
    exact hf (by simpa using hfd)
  rw [← hdlevel]
  omega

/-- Every surviving indecomposable has level at most the level of the
distinguished sink. -/
theorem objLevel_le_sink [IsAlgClosed k]
    (G : S.SkeletonHomGrading K)
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (hsink : D.multiplicity D.sink.1 = 1)
    (x : S.SurvivingLabel K) :
    G.objLevel R H hsink x ≤ G.objLevel R H hsink D.sink := by
  by_cases hx : x = D.sink
  · subst x
    exact le_rfl
  · have hex : ∃ f : S.factorObject K x ⟶ S.factorObject K D.sink,
        f ≠ 0 := by
      apply (Module.finrank_pos_iff_exists_ne_zero (R := k)).mp
      rw [PrimitiveMultiplicityInput.factorHomTo_finrank_eq_multiplicity
        (S := S) D x]
      exact PrimitiveMultiplicityInput.multiplicity_pos (S := S) D x
    obtain ⟨f, hf⟩ := hex
    apply Nat.le_of_lt
    apply G.objLevel_lt_of_nonzero_not_isIso R H hsink f hf
    intro hfi
    letI : IsIso f := hfi
    exact hx (S.factorObject_skeletal K ⟨asIso f⟩)

end SkeletonHomGrading

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
