import MagnitudeConjecture.CategoryTheory.TranslationQuiverOrbitGraph

/-!
# Nonperiodic translation routes

In a finite translation quiver with injective partial translation, every
nonperiodic tau-orbit is a finite path toward a projective boundary.  This file
chooses its first boundary time and proves that all preceding steps are the
literal partial translation.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.MeshCategory.RightMeshData.IsTauInjective

universe u

variable {Q : Type u} [Quiver.{u} Q]
variable (T : RightMeshData Q) (hT : T.IsTauInjective)

theorem exists_tauPermutation_pow_mem_projective_of_not_periodic
    [Finite Q] (x : Q) (hx : ¬ IsPeriodicVertex T x) :
    ∃ n : ℕ, (tauPermutation T hT ^ n) x ∈ T.projective := by
  obtain ⟨y, hy, hxy⟩ :=
    (not_isPeriodicVertex_iff_exists_projective_related T x).1 hx
  obtain ⟨n, hn⟩ :=
    (related_sameCycle T hT hxy).exists_nat_pow_eq
  exact ⟨n, hn.symm ▸ hy⟩

/-- The first forward permutation iterate at which a nonperiodic tau-component
hits the projective boundary.  Before this time the permutation agrees with
the literal partial translation. -/
noncomputable def tauBoundaryDepth [Finite Q]
    (x : Q) (hx : ¬ IsPeriodicVertex T x) : ℕ :=
  by
    classical
    exact Nat.find
      (exists_tauPermutation_pow_mem_projective_of_not_periodic T hT x hx)

theorem tauPermutation_pow_tauBoundaryDepth_mem_projective [Finite Q]
    (x : Q) (hx : ¬ IsPeriodicVertex T x) :
    (tauPermutation T hT ^ tauBoundaryDepth T hT x hx) x ∈
      T.projective := by
  classical
  exact Nat.find_spec
    (exists_tauPermutation_pow_mem_projective_of_not_periodic T hT x hx)

theorem tauPermutation_pow_lt_tauBoundaryDepth_not_mem_projective [Finite Q]
    (x : Q) (hx : ¬ IsPeriodicVertex T x) (n : ℕ)
    (hn : n < tauBoundaryDepth T hT x hx) :
    (tauPermutation T hT ^ n) x ∉ T.projective := by
  classical
  exact Nat.find_min
    (exists_tauPermutation_pow_mem_projective_of_not_periodic T hT x hx) hn

theorem tauBoundaryDepth_pos [Finite Q]
    (x : Q) (hx : ¬ IsPeriodicVertex T x)
    (hxp : x ∉ T.projective) :
    0 < tauBoundaryDepth T hT x hx := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hboundary :=
    tauPermutation_pow_tauBoundaryDepth_mem_projective T hT x hx
  exact hxp (by simpa [hzero] using hboundary)

theorem tauBoundaryDepth_eq_zero_iff [Finite Q]
    (x : Q) (hx : ¬ IsPeriodicVertex T x) :
    tauBoundaryDepth T hT x hx = 0 ↔ x ∈ T.projective := by
  constructor
  · intro hzero
    simpa [hzero] using
      (tauPermutation_pow_tauBoundaryDepth_mem_projective T hT x hx)
  · intro hprojective
    apply Nat.eq_zero_of_not_pos
    intro hpositive
    exact
      (tauPermutation_pow_lt_tauBoundaryDepth_not_mem_projective
        T hT x hx 0 hpositive) (by simpa using hprojective)

theorem tauBoundaryDepth_le_of_pow_mem_projective [Finite Q]
    (x : Q) (hx : ¬ IsPeriodicVertex T x) (n : ℕ)
    (hn : (tauPermutation T hT ^ n) x ∈ T.projective) :
    tauBoundaryDepth T hT x hx ≤ n := by
  by_contra hle
  exact
    (tauPermutation_pow_lt_tauBoundaryDepth_not_mem_projective
      T hT x hx n (Nat.lt_of_not_ge hle)) hn

theorem tauPermutation_pow_tau [Finite Q]
    (x : Q) (hxp : x ∉ T.projective) (n : ℕ) :
    (tauPermutation T hT ^ n) (T.tau ⟨x, hxp⟩) =
      (tauPermutation T hT ^ (n + 1)) x := by
  rw [← tauPermutation_apply_of_nonprojective T hT x hxp,
    pow_succ, Equiv.Perm.mul_apply]

/-- Advancing one literal tau-step decreases the remaining boundary depth by
one. -/
theorem tauBoundaryDepth_tau_add_one [Finite Q]
    (x : Q) (hx : ¬ IsPeriodicVertex T x) (hxp : x ∉ T.projective) :
    let s : {x : Q // x ∉ T.projective} := ⟨x, hxp⟩
    let hy : ¬ IsPeriodicVertex T (T.tau s) := fun hy ↦
      hx (isPeriodicVertex_of_related T hy
        ((tauOrbitSetoid T).symm (tau_related T s)))
    tauBoundaryDepth T hT (T.tau s) hy + 1 =
      tauBoundaryDepth T hT x hx := by
  dsimp only
  let s : {x : Q // x ∉ T.projective} := ⟨x, hxp⟩
  let hy : ¬ IsPeriodicVertex T (T.tau s) := fun hy ↦
    hx (isPeriodicVertex_of_related T hy
      ((tauOrbitSetoid T).symm (tau_related T s)))
  let dx := tauBoundaryDepth T hT x hx
  let dy := tauBoundaryDepth T hT (T.tau s) hy
  have hdxpos : 0 < dx := tauBoundaryDepth_pos T hT x hx hxp
  have hdxle : dx ≤ dy + 1 := by
    apply tauBoundaryDepth_le_of_pow_mem_projective T hT x hx
    rw [← tauPermutation_pow_tau T hT x hxp dy]
    exact tauPermutation_pow_tauBoundaryDepth_mem_projective
      T hT (T.tau s) hy
  have hdyle : dy ≤ dx - 1 := by
    apply tauBoundaryDepth_le_of_pow_mem_projective T hT (T.tau s) hy
    rw [tauPermutation_pow_tau T hT x hxp (dx - 1)]
    rw [Nat.sub_add_cancel hdxpos]
    exact tauPermutation_pow_tauBoundaryDepth_mem_projective T hT x hx
  change dy + 1 = dx
  apply Nat.le_antisymm
  · apply Nat.succ_le_iff.mpr
    exact lt_of_le_of_lt hdyle (Nat.sub_lt hdxpos (by omega))
  · exact hdxle

/-- Number of forward polarization steps from a nonperiodic arrow to its
projective-source boundary.  An endpoint at tau-depth `d` reaches the source
after `2*d` steps when it is currently the source and after `2*d+1` steps
when it is currently the target. -/
noncomputable def sigmaBoundaryDistance [Finite Q]
    {x y : Q} (hxy : ¬ (IsPeriodicVertex T x ∧ IsPeriodicVertex T y)) : ℕ := by
  classical
  by_cases hx : IsPeriodicVertex T x
  · have hy : ¬ IsPeriodicVertex T y := fun hy ↦ hxy ⟨hx, hy⟩
    exact 2 * tauBoundaryDepth T hT y hy + 1
  · by_cases hy : IsPeriodicVertex T y
    · exact 2 * tauBoundaryDepth T hT x hx
    · exact min (2 * tauBoundaryDepth T hT x hx)
        (2 * tauBoundaryDepth T hT y hy + 1)

theorem sigmaBoundaryDistance_of_source_periodic [Finite Q]
    {x y : Q} (hxy : ¬ (IsPeriodicVertex T x ∧ IsPeriodicVertex T y))
    (hx : IsPeriodicVertex T x) (hy : ¬ IsPeriodicVertex T y) :
    sigmaBoundaryDistance T hT hxy =
      2 * tauBoundaryDepth T hT y hy + 1 := by
  simp [sigmaBoundaryDistance, hx]

theorem sigmaBoundaryDistance_of_source_nonperiodic_target_periodic [Finite Q]
    {x y : Q} (hxy : ¬ (IsPeriodicVertex T x ∧ IsPeriodicVertex T y))
    (hx : ¬ IsPeriodicVertex T x) (hy : IsPeriodicVertex T y) :
    sigmaBoundaryDistance T hT hxy =
      2 * tauBoundaryDepth T hT x hx := by
  simp [sigmaBoundaryDistance, hx, hy]

theorem sigmaBoundaryDistance_of_both_nonperiodic [Finite Q]
    {x y : Q} (hxy : ¬ (IsPeriodicVertex T x ∧ IsPeriodicVertex T y))
    (hx : ¬ IsPeriodicVertex T x) (hy : ¬ IsPeriodicVertex T y) :
    sigmaBoundaryDistance T hT hxy =
      min (2 * tauBoundaryDepth T hT x hx)
        (2 * tauBoundaryDepth T hT y hy + 1) := by
  simp [sigmaBoundaryDistance, hx, hy]

/-- The sigma distance is zero exactly at a projective-source
representative. -/
theorem sigmaBoundaryDistance_eq_zero_iff [Finite Q]
    {x y : Q} (hxy : ¬ (IsPeriodicVertex T x ∧ IsPeriodicVertex T y)) :
    sigmaBoundaryDistance T hT hxy = 0 ↔ x ∈ T.projective := by
  classical
  by_cases hx : IsPeriodicVertex T x
  · have hy : ¬ IsPeriodicVertex T y := fun hy ↦ hxy ⟨hx, hy⟩
    have hxp : x ∉ T.projective :=
      hx x ((tauOrbitSetoid T).refl x)
    simp [sigmaBoundaryDistance, hx, hxp]
  · by_cases hy : IsPeriodicVertex T y
    · simp [sigmaBoundaryDistance, hx, hy,
        tauBoundaryDepth_eq_zero_iff T hT x hx]
    · simp [sigmaBoundaryDistance, hx, hy,
        tauBoundaryDepth_eq_zero_iff T hT x hx]

/-- Polarizing a nonperiodic arrow from a nonprojective source preserves
nonperiodicity of its endpoint pair. -/
theorem arrowTranslation_endpoint_nonperiodic
    {x y : Q} (hxy : ¬ (IsPeriodicVertex T x ∧ IsPeriodicVertex T y))
    (hxp : x ∉ T.projective) :
    ¬ (IsPeriodicVertex T y ∧
      IsPeriodicVertex T (T.tau ⟨x, hxp⟩)) := by
  rintro ⟨hy, htx⟩
  apply hxy
  exact ⟨isPeriodicVertex_of_related T htx
    ((tauOrbitSetoid T).symm (tau_related T ⟨x, hxp⟩)), hy⟩

theorem arrowTranslation_endpoint_nonperiodic_of_target
    {x y : Q} (hxp : x ∉ T.projective)
    (hxy : ¬ (IsPeriodicVertex T y ∧
      IsPeriodicVertex T (T.tau ⟨x, hxp⟩))) :
    ¬ (IsPeriodicVertex T x ∧ IsPeriodicVertex T y) := by
  rintro ⟨hx, hy⟩
  apply hxy
  exact ⟨hy, isPeriodicVertex_of_related T hx
    (tau_related T ⟨x, hxp⟩)⟩

theorem endpoint_nonperiodic_iff_of_arrowTranslationStep
    {a b : Arrow T} (hab : ArrowTranslationStep T hT a b) :
    (¬ (IsPeriodicVertex T a.1 ∧ IsPeriodicVertex T a.2.1)) ↔
      ¬ (IsPeriodicVertex T b.1 ∧ IsPeriodicVertex T b.2.1) := by
  rcases hab with ⟨⟨⟨x, hxp⟩, y, f⟩, rfl, rfl⟩
  exact ⟨fun hxy ↦ arrowTranslation_endpoint_nonperiodic T hxy hxp,
    fun hxy ↦
      arrowTranslation_endpoint_nonperiodic_of_target T hxp hxy⟩

theorem endpoint_nonperiodic_iff_of_arrowOrbit_related
    {a b : Arrow T} (hab : (arrowOrbitSetoid T hT) a b) :
    (¬ (IsPeriodicVertex T a.1 ∧ IsPeriodicVertex T a.2.1)) ↔
      ¬ (IsPeriodicVertex T b.1 ∧ IsPeriodicVertex T b.2.1) := by
  change Relation.EqvGen (ArrowTranslationStep T hT) a b at hab
  induction hab with
  | rel a b hab =>
      exact endpoint_nonperiodic_iff_of_arrowTranslationStep T hT hab
  | refl => exact Iff.rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- One forward polarization step decreases the sigma boundary distance by
exactly one. -/
theorem sigmaBoundaryDistance_translation_add_one [Finite Q]
    {x y : Q} (hxy : ¬ (IsPeriodicVertex T x ∧ IsPeriodicVertex T y))
    (hxp : x ∉ T.projective) :
    sigmaBoundaryDistance T hT
        (arrowTranslation_endpoint_nonperiodic T hxy hxp) + 1 =
      sigmaBoundaryDistance T hT hxy := by
  classical
  let s : {x : Q // x ∉ T.projective} := ⟨x, hxp⟩
  by_cases hx : IsPeriodicVertex T x
  · have hy : ¬ IsPeriodicVertex T y := fun hy ↦ hxy ⟨hx, hy⟩
    have htx : IsPeriodicVertex T (T.tau s) :=
      isPeriodicVertex_of_related T hx (tau_related T s)
    rw [sigmaBoundaryDistance_of_source_nonperiodic_target_periodic
        T hT (arrowTranslation_endpoint_nonperiodic T hxy hxp) hy htx,
      sigmaBoundaryDistance_of_source_periodic T hT hxy hx hy]
  · have htx : ¬ IsPeriodicVertex T (T.tau s) := fun htx ↦
      hx (isPeriodicVertex_of_related T htx
        ((tauOrbitSetoid T).symm (tau_related T s)))
    have hdepth := tauBoundaryDepth_tau_add_one T hT x hx hxp
    by_cases hy : IsPeriodicVertex T y
    · rw [sigmaBoundaryDistance_of_source_periodic
          T hT (arrowTranslation_endpoint_nonperiodic T hxy hxp) hy htx,
        sigmaBoundaryDistance_of_source_nonperiodic_target_periodic
          T hT hxy hx hy]
      omega
    · rw [sigmaBoundaryDistance_of_both_nonperiodic
          T hT (arrowTranslation_endpoint_nonperiodic T hxy hxp) hy htx,
        sigmaBoundaryDistance_of_both_nonperiodic T hT hxy hx hy]
      by_cases hle :
          tauBoundaryDepth T hT x hx ≤ tauBoundaryDepth T hT y hy
      · rw [min_eq_right (by omega), min_eq_left (by omega)]
        omega
      · rw [min_eq_left (by omega), min_eq_right (by omega)]

/-- Concrete arrows with at least one nonperiodic endpoint. -/
abbrev NonperiodicArrow :=
  {a : Arrow T //
    ¬ (IsPeriodicVertex T a.1 ∧ IsPeriodicVertex T a.2.1)}

/-- One forward polarization of a nonperiodic arrow whose source is not
projective. -/
def nonperiodicArrowForward [Finite Q]
    (a : NonperiodicArrow T) (ha : a.1.1 ∉ T.projective) :
    NonperiodicArrow T := by
  let s : SourceArrow T := ⟨⟨a.1.1, ha⟩, a.1.2.1, a.1.2.2⟩
  exact ⟨(arrowTranslationEquiv T hT s).forget,
    arrowTranslation_endpoint_nonperiodic T a.2 ha⟩

theorem nonperiodicArrowForward_orbit [Finite Q]
    (a : NonperiodicArrow T) (ha : a.1.1 ∉ T.projective) :
    Quotient.mk (arrowOrbitSetoid T hT)
        (nonperiodicArrowForward T hT a ha).1 =
      Quotient.mk (arrowOrbitSetoid T hT) a.1 := by
  let s : SourceArrow T := ⟨⟨a.1.1, ha⟩, a.1.2.1, a.1.2.2⟩
  exact (Quotient.sound (arrowTranslation_related T hT s)).symm

theorem nonperiodicArrowForward_distance_add_one [Finite Q]
    (a : NonperiodicArrow T) (ha : a.1.1 ∉ T.projective) :
    sigmaBoundaryDistance T hT
        (nonperiodicArrowForward T hT a ha).2 + 1 =
      sigmaBoundaryDistance T hT a.2 := by
  exact sigmaBoundaryDistance_translation_add_one T hT a.2 ha

/-- A projective-source boundary arrow in the same sigma-orbit as a given
nonperiodic arrow. -/
structure SigmaBoundaryNormalForm [Finite Q]
    (a : NonperiodicArrow T) where
  boundary : NonperiodicArrow T
  source_projective : boundary.1.1 ∈ T.projective
  orbit_eq :
    Quotient.mk (arrowOrbitSetoid T hT) boundary.1 =
      Quotient.mk (arrowOrbitSetoid T hT) a.1

private noncomputable def sigmaBoundaryNormalFormAux [Finite Q]
    (a : NonperiodicArrow T) : SigmaBoundaryNormalForm T hT a := by
  by_cases hsource : a.1.1 ∈ T.projective
  · exact ⟨a, hsource, rfl⟩
  · let b := nonperiodicArrowForward T hT a hsource
    let normal := sigmaBoundaryNormalFormAux b
    exact ⟨normal.boundary, normal.source_projective,
      normal.orbit_eq.trans
        (nonperiodicArrowForward_orbit T hT a hsource)⟩
termination_by sigmaBoundaryDistance T hT a.2
decreasing_by
  have hstep :=
    nonperiodicArrowForward_distance_add_one T hT a hsource
  omega

/-- Normalize a nonperiodic arrow by repeatedly polarizing it to its unique
projective-source end. -/
noncomputable def sigmaBoundaryNormalForm [Finite Q]
    (a : NonperiodicArrow T) : SigmaBoundaryNormalForm T hT a :=
  sigmaBoundaryNormalFormAux T hT a

theorem sigmaBoundaryNormalForm_boundary_of_source_projective [Finite Q]
    (a : NonperiodicArrow T) (ha : a.1.1 ∈ T.projective) :
    (sigmaBoundaryNormalForm T hT a).boundary = a := by
  rw [sigmaBoundaryNormalForm, sigmaBoundaryNormalFormAux]
  simp only [ha, ↓reduceDIte]

theorem sigmaBoundaryNormalForm_boundary_forward [Finite Q]
    (a : NonperiodicArrow T) (ha : a.1.1 ∉ T.projective) :
    (sigmaBoundaryNormalForm T hT a).boundary =
      (sigmaBoundaryNormalForm T hT
        (nonperiodicArrowForward T hT a ha)).boundary := by
  rw [sigmaBoundaryNormalForm, sigmaBoundaryNormalFormAux]
  simp only [ha, ↓reduceDIte]
  rw [sigmaBoundaryNormalForm]

theorem sigmaBoundaryNormalForm_boundary_step [Finite Q]
    {a b : Arrow T}
    (ha : ¬ (IsPeriodicVertex T a.1 ∧ IsPeriodicVertex T a.2.1))
    (hb : ¬ (IsPeriodicVertex T b.1 ∧ IsPeriodicVertex T b.2.1))
    (hab : ArrowTranslationStep T hT a b) :
    (sigmaBoundaryNormalForm T hT ⟨a, ha⟩).boundary =
      (sigmaBoundaryNormalForm T hT ⟨b, hb⟩).boundary := by
  rcases hab with ⟨⟨⟨x, hxp⟩, y, f⟩, rfl, rfl⟩
  change
    (sigmaBoundaryNormalForm T hT
        (⟨(⟨x, y, f⟩ : Arrow T), ha⟩ : NonperiodicArrow T)).boundary =
      (sigmaBoundaryNormalForm T hT
        ⟨(arrowTranslationEquiv T hT
          (⟨⟨x, hxp⟩, y, f⟩ : SourceArrow T)).forget, hb⟩).boundary
  simpa only [nonperiodicArrowForward] using
    sigmaBoundaryNormalForm_boundary_forward T hT
      (⟨(⟨x, y, f⟩ : Arrow T), ha⟩ : NonperiodicArrow T) hxp

theorem sigmaBoundaryNormalForm_boundary_eq_of_related [Finite Q]
    {a b : Arrow T}
    (ha : ¬ (IsPeriodicVertex T a.1 ∧ IsPeriodicVertex T a.2.1))
    (hb : ¬ (IsPeriodicVertex T b.1 ∧ IsPeriodicVertex T b.2.1))
    (hab : (arrowOrbitSetoid T hT) a b) :
    (sigmaBoundaryNormalForm T hT ⟨a, ha⟩).boundary =
      (sigmaBoundaryNormalForm T hT ⟨b, hb⟩).boundary := by
  change Relation.EqvGen (ArrowTranslationStep T hT) a b at hab
  induction hab with
  | rel a b hab =>
      exact sigmaBoundaryNormalForm_boundary_step T hT ha hb hab
  | refl => rfl
  | symm a b hab ih => exact (ih hb ha).symm
  | trans a b c hab hbc ih₁ ih₂ =>
      have hb' :
          ¬ (IsPeriodicVertex T b.1 ∧ IsPeriodicVertex T b.2.1) :=
        (endpoint_nonperiodic_iff_of_arrowOrbit_related T hT hab).1 ha
      exact (ih₁ ha hb').trans (ih₂ hb' hb)

/-- A nonperiodic sigma-orbit has only one projective-source arrow. -/
theorem source_projective_arrow_unique_in_nonperiodic_orbit [Finite Q]
    {a b : Arrow T}
    (ha : ¬ (IsPeriodicVertex T a.1 ∧ IsPeriodicVertex T a.2.1))
    (hb : ¬ (IsPeriodicVertex T b.1 ∧ IsPeriodicVertex T b.2.1))
    (hap : a.1 ∈ T.projective) (hbp : b.1 ∈ T.projective)
    (hab : (arrowOrbitSetoid T hT) a b) : a = b := by
  have hnormal :=
    sigmaBoundaryNormalForm_boundary_eq_of_related T hT ha hb hab
  rw [sigmaBoundaryNormalForm_boundary_of_source_projective T hT ⟨a, ha⟩ hap,
    sigmaBoundaryNormalForm_boundary_of_source_projective T hT ⟨b, hb⟩ hbp]
    at hnormal
  exact congrArg Subtype.val hnormal

theorem arrowOrbitRepresentative_endpoint_nonperiodic
    (e : ArrowOrbit T hT)
    (he : ¬
      (IsPeriodicTauOrbit T (arrowOrbitSource T hT e) ∧
        IsPeriodicTauOrbit T (arrowOrbitTarget T hT e))) :
    ¬ (IsPeriodicVertex T (arrowOrbitRepresentative T hT e).1 ∧
      IsPeriodicVertex T (arrowOrbitRepresentative T hT e).2.1) := by
  simpa only [arrowOrbitSource, arrowOrbitTarget,
    isPeriodicTauOrbit_tauClass] using he

end MagnitudeConjecture.MeshCategory.RightMeshData.IsTauInjective
