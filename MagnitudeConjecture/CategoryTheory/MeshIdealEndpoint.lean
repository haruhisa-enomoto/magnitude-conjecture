import MagnitudeConjecture.CategoryTheory.LinearPathIncoming
import MagnitudeConjecture.CategoryTheory.MeshCategory

/-!
# Endpoint normal forms for the ordinary mesh ideal

At a fixed target, a mesh-ideal element is a left multiple of the mesh
relation at that target, when it exists, plus ideal-valued coefficients
followed by the incoming arrows.  At a projective target the first summand is
absent.  The proof expands the right path-basis multiplier and peels its first
reverse-quiver arrow.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped BigOperators

namespace MagnitudeConjecture.MeshCategory

open QuotientSubmoduleEquidistribution.CategoricalIdeal

universe u v w

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]
variable [∀ x : Q, Fintype (Σ y : Q, x ⟶ y)]

namespace RightMeshData

variable (T : RightMeshData Q)

private abbrev freeObj (x : Q) :=
  MagnitudeConjecture.LinearPathCategory.obj k Q x

/-- The generated mesh-ideal submodule in one free-category Hom space. -/
abbrev meshIdealHom (x z : Q) : Submodule k (freeObj (k := k) x ⟶ freeObj (k := k) z) :=
  HomIdeal.generatedHomSubmodule k (T.meshGeneratorSet (k := k))
    (freeObj (k := k) x) (freeObj (k := k) z)

/-- Endpoint normal form when the target carries a mesh relation. -/
def HasNonprojectiveEndingNormalForm
    (z : {z : Q // z ∉ T.projective}) (x : Q)
    (f : freeObj (k := k) x ⟶ freeObj (k := k) z.1) : Prop :=
  ∃ (a : freeObj (k := k) x ⟶ freeObj (k := k) (T.tau z))
    (g : MagnitudeConjecture.LinearPathCategory.IncomingCoefficient
      (k := k) x z.1),
    (∀ b, g b ∈ T.meshIdealHom (k := k) x b.1) ∧
      f = a ≫ T.meshRelation (k := k) z +
        MagnitudeConjecture.LinearPathCategory.incomingSum g

/-- Endpoint normal form at a projective target. -/
def HasProjectiveEndingNormalForm
    (z : Q) (x : Q)
    (f : freeObj (k := k) x ⟶ freeObj (k := k) z) : Prop :=
  ∃ g : MagnitudeConjecture.LinearPathCategory.IncomingCoefficient
      (k := k) x z,
    (∀ b, g b ∈ T.meshIdealHom (k := k) x b.1) ∧
      f = MagnitudeConjecture.LinearPathCategory.incomingSum g

private theorem meshComposite_mem_ideal
    {x a b : Q}
    (r : freeObj (k := k) a ⟶ freeObj (k := k) b)
    (hr : r ∈ T.meshGeneratorSet (k := k)
      (freeObj (k := k) a) (freeObj (k := k) b))
    (p : Quiver.Path a x) {y : Q} (q : Quiver.Path y b) :
    MagnitudeConjecture.LinearPathCategory.pathHom p ≫ r ≫
        MagnitudeConjecture.LinearPathCategory.pathHom q ∈
      T.meshIdealHom (k := k) x y := by
  exact HomIdeal.composite_mem_linearSpan (T.meshGeneratorSet (k := k))
    (MagnitudeConjecture.LinearPathCategory.pathHom p) hr
    (MagnitudeConjecture.LinearPathCategory.pathHom q)

private theorem basisComposite_hasNonprojectiveEndingNormalForm
    (z : {z : Q // z ∉ T.projective}) (x : Q)
    {f : freeObj (k := k) x ⟶ freeObj (k := k) z.1}
    (hf : f ∈ MagnitudeConjecture.LinearPathCategory.basisCompositeSet
      (T.meshGeneratorSet (k := k))
      (freeObj (k := k) x) (freeObj (k := k) z.1)) :
    T.HasNonprojectiveEndingNormalForm (k := k) z x f := by
  classical
  rcases hf with ⟨A, B, r, hr, p, q, rfl⟩
  rcases hr with ⟨s, hA, hB, hr⟩
  subst A
  subst B
  subst r
  by_cases hq : q.length = 0
  · have hzs : z.1 = s.1 := q.eq_of_length_zero hq
    have hzs' : z = s := Subtype.ext hzs
    subst s
    have hqnil : q = Quiver.Path.nil := q.eq_nil_of_length_zero hq
    subst q
    refine ⟨MagnitudeConjecture.LinearPathCategory.pathHom p, 0, ?_, ?_⟩
    · intro b
      exact (T.meshIdealHom (k := k) x b.1).zero_mem
    · rw [MagnitudeConjecture.LinearPathCategory.incomingSum]
      simp
  · obtain ⟨y, e, q', hq', _⟩ :=
      (Quiver.Path.length_ne_zero_iff_eq_comp q).mp hq
    subst q
    let b₀ : MagnitudeConjecture.LinearPathCategory.IncomingArrow z.1 := ⟨y, e⟩
    let c : freeObj (k := k) x ⟶ freeObj (k := k) y :=
      MagnitudeConjecture.LinearPathCategory.pathHom p ≫
        T.meshRelation (k := k) s ≫
          MagnitudeConjecture.LinearPathCategory.pathHom q'
    have hc : c ∈ T.meshIdealHom (k := k) x y := by
      exact T.meshComposite_mem_ideal
        (T.meshRelation (k := k) s)
        (T.meshRelation_mem_meshGeneratorSet (k := k) s) p q'
    let g := MagnitudeConjecture.LinearPathCategory.singleIncomingCoefficient
      (k := k) b₀ c
    refine ⟨0, g, ?_, ?_⟩
    · intro b
      by_cases hb : b₀ = b
      · subst b
        rw [show g b₀ = c by
          simp [g,
            MagnitudeConjecture.LinearPathCategory.singleIncomingCoefficient]]
        exact hc
      · have hgb : g b = 0 := by
          simp [g,
            MagnitudeConjecture.LinearPathCategory.singleIncomingCoefficient,
            hb]
        rw [hgb]
        exact (T.meshIdealHom (k := k) x b.1).zero_mem
    · simp only [Limits.zero_comp, zero_add]
      rw [MagnitudeConjecture.LinearPathCategory.incomingSum_single]
      dsimp only [c, b₀]
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      simp only [Category.assoc]
      rw [MagnitudeConjecture.LinearPathCategory.pathHom_comp]
      rfl

private theorem basisComposite_hasProjectiveEndingNormalForm
    (z : Q) (hz : z ∈ T.projective) (x : Q)
    {f : freeObj (k := k) x ⟶ freeObj (k := k) z}
    (hf : f ∈ MagnitudeConjecture.LinearPathCategory.basisCompositeSet
      (T.meshGeneratorSet (k := k))
      (freeObj (k := k) x) (freeObj (k := k) z)) :
    T.HasProjectiveEndingNormalForm (k := k) z x f := by
  classical
  rcases hf with ⟨A, B, r, hr, p, q, rfl⟩
  rcases hr with ⟨s, hA, hB, hr⟩
  subst A
  subst B
  subst r
  have hq : q.length ≠ 0 := by
    intro hzero
    have hzs : z = s.1 := q.eq_of_length_zero hzero
    subst z
    exact s.2 hz
  obtain ⟨y, e, q', hq', _⟩ :=
    (Quiver.Path.length_ne_zero_iff_eq_comp q).mp hq
  subst q
  let b₀ : MagnitudeConjecture.LinearPathCategory.IncomingArrow z := ⟨y, e⟩
  let c : freeObj (k := k) x ⟶ freeObj (k := k) y :=
    MagnitudeConjecture.LinearPathCategory.pathHom p ≫
      T.meshRelation (k := k) s ≫
        MagnitudeConjecture.LinearPathCategory.pathHom q'
  have hc : c ∈ T.meshIdealHom (k := k) x y := by
    exact T.meshComposite_mem_ideal
      (T.meshRelation (k := k) s)
      (T.meshRelation_mem_meshGeneratorSet (k := k) s) p q'
  let g := MagnitudeConjecture.LinearPathCategory.singleIncomingCoefficient
    (k := k) b₀ c
  refine ⟨g, ?_, ?_⟩
  · intro b
    by_cases hb : b₀ = b
    · subst b
      rw [show g b₀ = c by
        simp [g,
          MagnitudeConjecture.LinearPathCategory.singleIncomingCoefficient]]
      exact hc
    · have hgb : g b = 0 := by
        simp [g,
          MagnitudeConjecture.LinearPathCategory.singleIncomingCoefficient,
          hb]
      rw [hgb]
      exact (T.meshIdealHom (k := k) x b.1).zero_mem
  · rw [MagnitudeConjecture.LinearPathCategory.incomingSum_single]
    dsimp only [c, b₀]
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    simp only [Category.assoc]
    rw [MagnitudeConjecture.LinearPathCategory.pathHom_comp]
    rfl

private theorem hasNonprojectiveEndingNormalForm_zero
    (z : {z : Q // z ∉ T.projective}) (x : Q) :
    T.HasNonprojectiveEndingNormalForm (k := k) z x 0 := by
  refine ⟨0, 0, ?_, ?_⟩
  · intro b
    exact (T.meshIdealHom (k := k) x b.1).zero_mem
  · simp [MagnitudeConjecture.LinearPathCategory.incomingSum]

private theorem HasNonprojectiveEndingNormalForm.add
    (z : {z : Q // z ∉ T.projective}) (x : Q)
    {f g : freeObj (k := k) x ⟶ freeObj (k := k) z.1}
    (hf : T.HasNonprojectiveEndingNormalForm (k := k) z x f)
    (hg : T.HasNonprojectiveEndingNormalForm (k := k) z x g) :
    T.HasNonprojectiveEndingNormalForm (k := k) z x (f + g) := by
  rcases hf with ⟨a, c, hc, rfl⟩
  rcases hg with ⟨b, d, hd, rfl⟩
  refine ⟨a + b, c + d, ?_, ?_⟩
  · intro e
    exact (T.meshIdealHom (k := k) x e.1).add_mem (hc e) (hd e)
  · simp only [Preadditive.add_comp, Pi.add_apply,
      MagnitudeConjecture.LinearPathCategory.incomingSum,
      Finset.sum_add_distrib]
    abel

private theorem HasNonprojectiveEndingNormalForm.smul
    (z : {z : Q // z ∉ T.projective}) (x : Q) (r : k)
    {f : freeObj (k := k) x ⟶ freeObj (k := k) z.1}
    (hf : T.HasNonprojectiveEndingNormalForm (k := k) z x f) :
    T.HasNonprojectiveEndingNormalForm (k := k) z x (r • f) := by
  rcases hf with ⟨a, c, hc, rfl⟩
  refine ⟨r • a, r • c, ?_, ?_⟩
  · intro e
    exact (T.meshIdealHom (k := k) x e.1).smul_mem r (hc e)
  · simp [MagnitudeConjecture.LinearPathCategory.incomingSum,
      CategoryTheory.Linear.smul_comp, Finset.smul_sum, smul_add]

private theorem hasProjectiveEndingNormalForm_zero
    (z x : Q) : T.HasProjectiveEndingNormalForm (k := k) z x 0 := by
  refine ⟨0, ?_, ?_⟩
  · intro b
    exact (T.meshIdealHom (k := k) x b.1).zero_mem
  · simp [MagnitudeConjecture.LinearPathCategory.incomingSum]

private theorem HasProjectiveEndingNormalForm.add
    (z x : Q) {f g : freeObj (k := k) x ⟶ freeObj (k := k) z}
    (hf : T.HasProjectiveEndingNormalForm (k := k) z x f)
    (hg : T.HasProjectiveEndingNormalForm (k := k) z x g) :
    T.HasProjectiveEndingNormalForm (k := k) z x (f + g) := by
  rcases hf with ⟨c, hc, rfl⟩
  rcases hg with ⟨d, hd, rfl⟩
  refine ⟨c + d, ?_, ?_⟩
  · intro e
    exact (T.meshIdealHom (k := k) x e.1).add_mem (hc e) (hd e)
  · simp [MagnitudeConjecture.LinearPathCategory.incomingSum,
      Finset.sum_add_distrib]

private theorem HasProjectiveEndingNormalForm.smul
    (z x : Q) (r : k)
    {f : freeObj (k := k) x ⟶ freeObj (k := k) z}
    (hf : T.HasProjectiveEndingNormalForm (k := k) z x f) :
    T.HasProjectiveEndingNormalForm (k := k) z x (r • f) := by
  rcases hf with ⟨c, hc, rfl⟩
  refine ⟨r • c, ?_, ?_⟩
  · intro e
    exact (T.meshIdealHom (k := k) x e.1).smul_mem r (hc e)
  · simp [MagnitudeConjecture.LinearPathCategory.incomingSum,
      CategoryTheory.Linear.smul_comp, Finset.smul_sum]

/-- Every mesh-ideal element ending at a nonprojective vertex has the exact
endpoint normal form. -/
theorem meshIdeal_hasNonprojectiveEndingNormalForm
    (z : {z : Q // z ∉ T.projective}) (x : Q)
    {f : freeObj (k := k) x ⟶ freeObj (k := k) z.1}
    (hf : f ∈ T.meshIdealHom (k := k) x z.1) :
    T.HasNonprojectiveEndingNormalForm (k := k) z x f := by
  change f ∈ HomIdeal.generatedHomSubmodule k (T.meshGeneratorSet (k := k))
    (freeObj (k := k) x) (freeObj (k := k) z.1) at hf
  rw [MagnitudeConjecture.LinearPathCategory.generatedHomSubmodule_eq_span_basisCompositeSet]
    at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
      exact T.basisComposite_hasNonprojectiveEndingNormalForm z x hf
  | zero => exact T.hasNonprojectiveEndingNormalForm_zero z x
  | add f g _ _ hf hg => exact hf.add T z x hg
  | smul r f _ hf => exact hf.smul T z x r

/-- Every mesh-ideal element ending at a projective vertex is an incoming sum
with ideal-valued coefficients; no endpoint mesh relation occurs. -/
theorem meshIdeal_hasProjectiveEndingNormalForm
    (z : Q) (hz : z ∈ T.projective) (x : Q)
    {f : freeObj (k := k) x ⟶ freeObj (k := k) z}
    (hf : f ∈ T.meshIdealHom (k := k) x z) :
    T.HasProjectiveEndingNormalForm (k := k) z x f := by
  change f ∈ HomIdeal.generatedHomSubmodule k (T.meshGeneratorSet (k := k))
    (freeObj (k := k) x) (freeObj (k := k) z) at hf
  rw [MagnitudeConjecture.LinearPathCategory.generatedHomSubmodule_eq_span_basisCompositeSet]
    at hf
  induction hf using Submodule.span_induction with
  | mem f hf => exact T.basisComposite_hasProjectiveEndingNormalForm z hz x hf
  | zero => exact T.hasProjectiveEndingNormalForm_zero z x
  | add f g _ _ hf hg => exact hf.add T z x hg
  | smul r f _ hf => exact hf.smul T z x r

/-- A free morphism maps to zero in the mesh quotient exactly when it lies in
the generated mesh ideal. -/
theorem quotient_map_eq_zero_iff_mem_meshIdealHom
    (x z : Q) (f : freeObj (k := k) x ⟶ freeObj (k := k) z) :
    (quotientFunctor (k := k) T).map f = 0 ↔
      f ∈ T.meshIdealHom (k := k) x z := by
  change (quotientFunctor (k := k) T).map f = 0 ↔
    f ∈ HomIdeal.generatedHomSubmodule k (T.meshGeneratorSet (k := k))
      (freeObj (k := k) x) (freeObj (k := k) z)
  exact (MagnitudeConjecture.LinearPathCategory.HomogeneousQuotient.relationIdeal
    (T.meshGeneratorSet (k := k))).map_eq_zero_iff f

end RightMeshData

end MagnitudeConjecture.MeshCategory
