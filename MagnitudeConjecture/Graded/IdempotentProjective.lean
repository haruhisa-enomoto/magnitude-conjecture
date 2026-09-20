import MagnitudeConjecture.Graded.RegularModule

/-! # Homogeneous maps from the projective attached to an idempotent -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.Graded
variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- The principal left ideal Ae as the image of right multiplication by e. -/
abbrev principalProjective (e : A) : Submodule A A :=
  (LinearMap.toSpanSingleton A A e).range

/-- The canonical generator of Ae. -/
def principalGenerator (e : A) : principalProjective e := ⟨e, ⟨1, one_mul e⟩⟩

theorem principal_fixed {e : A} (he : e * e = e) (x : principalProjective e) : x.val * e = x.val := by
  obtain ⟨a, ha⟩ := x.property
  change a * e = x.val at ha
  rw [← ha, mul_assoc, he]

variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable [FiniteDimensional k A]

/-- Right multiplication by a degree-zero element is homogeneous of degree zero. -/
theorem principalMap_homogeneous (e : A) (he : e ∈ R.component 0) :
    (R.regularModuleGrading hmul).Homogeneous (R.regularModuleGrading hmul) 0
      (LinearMap.toSpanSingleton A A e) := by
  intro i a ha
  exact hmul ha he

/-- The induced grading of the actual principal projective module. -/
def principalProjectiveGrading (e : A) (he : e ∈ R.component 0) :
    ModuleGrading (M := principalProjective e) R :=
  (R.regularModuleGrading hmul).rangeGrading (R.regularModuleGrading hmul)
    (LinearMap.toSpanSingleton A A e) (principalMap_homogeneous R hmul e he)

variable {M : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable (G : ModuleGrading (M := M) R)

/-- The e-coordinate of a homogeneous component. -/
def idempotentComponent (e : A) (d : ℤ) : Submodule k M where
  carrier := {x | x ∈ G.component d ∧ e • x = x}
  zero_mem' := ⟨(G.component d).zero_mem, smul_zero e⟩
  add_mem' := fun hx hy ↦ ⟨(G.component d).add_mem hx.1 hy.1, by
    rw [smul_add, hx.2, hy.2]⟩
  smul_mem' := fun c x hx ↦ ⟨(G.component d).smul_mem c hx.1, by
    rw [smul_comm e c x, hx.2]⟩

/-- A vector fixed by e determines the unique module map from Ae taking e to it. -/
def principalMap (e : A) (x : M) : principalProjective e →ₗ[A] M where
  toFun z := z.val • x
  map_add' z w := add_smul z.val w.val x
  map_smul' a z := mul_smul a z.val x

/-- Evaluation at the idempotent identifies homogeneous maps with its coordinate space. -/
def principalHomEquiv (e : A) (he : e * e = e) (he0 : e ∈ R.component 0) (d : ℤ) :
    (principalProjectiveGrading R hmul e he0).homComponent G d ≃ₗ[k]
      idempotentComponent R G e d where
  toFun f := ⟨f.val (principalGenerator e), ⟨by
      simpa only [zero_add] using f.property 0 (principalGenerator e) he0,
    by
      rw [← f.val.map_smul]
      congr 1
      apply Subtype.ext
      exact he⟩⟩
  invFun x := ⟨principalMap e x.val, by
    intro i z hz
    exact G.smul_mem hz x.property.1⟩
  left_inv f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro z
    change z.val • f.val (principalGenerator e) = f.val z
    rw [← f.val.map_smul]
    congr 1
    apply Subtype.ext
    exact principal_fixed he z
  right_inv x := by
    apply Subtype.ext
    exact x.property.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end MagnitudeConjecture.Graded
