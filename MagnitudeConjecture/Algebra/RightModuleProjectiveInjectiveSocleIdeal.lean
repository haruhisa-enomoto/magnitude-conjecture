import MagnitudeConjecture.Algebra.RightModuleInjectiveSocle
import MagnitudeConjecture.Algebra.RightModuleIdealQuotientSkeleton
import MagnitudeConjecture.Algebra.RightModuleRegularDecomposition
import MagnitudeConjecture.Algebra.RightModuleSupportQuotient
import MagnitudeConjecture.CategoryTheory.FiniteKrullSchmidtMatrix
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Socle ideals of primitive projective-injective right modules

Let `eA` be one member of a complete duplicate-free family of primitive
projective right ideals.  If `eA` is injective, then its socle, embedded in
the regular right module, is stable under left multiplication and hence is a
two-sided ideal.  This is the algebraic first step of the rejection lemma.

The proof is the Auslander--Reiten argument in coordinates.  A nonzero
off-diagonal component `eA → fA` on the simple essential socle would be monic;
injectivity of `eA` would split it; and indecomposability of `fA` would then
make the two selected primitive projectives isomorphic, contradicting the
duplicate-free skeleton.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped BigOperators ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

namespace PrimitiveProjectivePresentation

variable (P : S.PrimitiveProjectivePresentation)

/-- The socle of the selected primitive projective `p`, embedded in the
right regular module. -/
def primitiveProjectiveSocleSubmodule
    (p : S.ProjectiveLabel) : Submodule Aᵐᵒᵖ A :=
  (moduleSocle Aᵐᵒᵖ
      (RightModule.rightIdealFGObj (P.idempotent p))).map
    (RightModule.rightIdeal (P.idempotent p)).subtype

/-- The `(q,p)` coordinate of left multiplication by `a`, restricted from
`pA` to `qA`. -/
def primitiveLeftActionComponent
    (p q : S.ProjectiveLabel) (a : A) :
    RightModule.rightIdealFGObj (P.idempotent p) ⟶
      RightModule.rightIdealFGObj (P.idempotent q) := by
  letI : Module.Finite Aᵐᵒᵖ A :=
    Module.Finite.equiv RightModule.rightRegularLinearEquiv
  letI : IsNoetherian Aᵐᵒᵖ A := inferInstance
  letI : Module.Finite Aᵐᵒᵖ
      (RightModule.rightIdeal (P.idempotent p)) := inferInstance
  letI : Module.Finite Aᵐᵒᵖ
      (RightModule.rightIdeal (P.idempotent q)) := inferInstance
  let f : RightModule.rightIdeal (P.idempotent p) →ₗ[Aᵐᵒᵖ]
      RightModule.rightIdeal (P.idempotent q) :=
    ((RightModule.rightRegularLeftMul (P.idempotent q * a)).domRestrict
      (RightModule.rightIdeal (P.idempotent p))).codRestrict
        (RightModule.rightIdeal (P.idempotent q)) fun x ↦
          ⟨a * x.1, (mul_assoc (P.idempotent q) a x.1).symm⟩
  exact FGModuleCat.ofHom f

@[simp]
theorem primitiveLeftActionComponent_apply_val
    (p q : S.ProjectiveLabel) (a : A)
    (x : RightModule.rightIdealFGObj (P.idempotent p)) :
    ((P.primitiveLeftActionComponent p q a).hom.hom x).1 =
      P.idempotent q * (a * x.1) :=
  mul_assoc (P.idempotent q) a x.1

/-- Every off-diagonal left-action component kills the socle of a selected
primitive projective-injective. -/
theorem moduleSocleInclusion_comp_primitiveLeftActionComponent_eq_zero
    (p q : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hpq : q ≠ p) (a : A) :
    MagnitudeConjecture.moduleSocleInclusion
        (RightModule.rightIdealFGObj (P.idempotent p)) ≫
      P.primitiveLeftActionComponent p q a = 0 := by
  let pIso := P.primitiveProjectiveIso p
  letI : Injective
      (RightModule.rightIdealFGObj (P.idempotent p)) :=
    Injective.of_iso pIso.symm hpInjective
  let hPind : Indecomposable
      (RightModule.rightIdealFGObj (P.idempotent p)) :=
    RightModule.rightIdealFGObj_indecomposable (P.primitive p)
  let hQind : Indecomposable
      (RightModule.rightIdealFGObj (P.idempotent q)) :=
    RightModule.rightIdealFGObj_indecomposable (P.primitive q)
  apply MagnitudeConjecture.moduleSocleInclusion_comp_eq_zero_of_not_iso
    (k := k) _ _ hPind hQind
  · rintro ⟨fIso⟩
    have hsources :
        S.primitiveSourceLabel (P.primitive p) =
          S.primitiveSourceLabel (P.primitive q) :=
      S.fgObj_skeletal
        ⟨(S.primitiveSourceIso (P.primitive p)).symm ≪≫
          fIso ≪≫ S.primitiveSourceIso (P.primitive q)⟩
    have hpq' : p = q := by
      cases p with
      | mk pi hpi =>
        cases q with
        | mk qi hqi =>
          have hsourceP :
              S.primitiveSourceLabel (P.primitive ⟨pi, hpi⟩) = pi :=
            congrArg ProjectiveLabel.label (P.sourceLabel ⟨pi, hpi⟩)
          have hsourceQ :
              S.primitiveSourceLabel (P.primitive ⟨qi, hqi⟩) = qi :=
            congrArg ProjectiveLabel.label (P.sourceLabel ⟨qi, hqi⟩)
          have hpiqi : pi = qi :=
            hsourceP.symm.trans (hsources.trans hsourceQ)
          subst qi
          rfl
    exact hpq hpq'.symm

/-- Left multiplication preserves the embedded socle of a selected
primitive projective-injective. -/
theorem mul_mem_primitiveProjectiveSocleSubmodule
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    {a x : A} (hx : x ∈ P.primitiveProjectiveSocleSubmodule p) :
    a * x ∈ P.primitiveProjectiveSocleSubmodule p := by
  classical
  let pIso := P.primitiveProjectiveIso p
  letI : Injective
      (RightModule.rightIdealFGObj (P.idempotent p)) :=
    Injective.of_iso pIso.symm hpInjective
  change x ∈
    (moduleSocle Aᵐᵒᵖ
      (RightModule.rightIdealFGObj (P.idempotent p))).map
        (RightModule.rightIdeal (P.idempotent p)).subtype at hx
  obtain ⟨y, hySocle, hyx⟩ := (Submodule.mem_map).1 hx
  have hdiagonalSocle :
      (P.primitiveLeftActionComponent p p a).hom.hom y ∈
        moduleSocle Aᵐᵒᵖ
          (RightModule.rightIdealFGObj (P.idempotent p)) :=
    map_moduleSocle_le
      (P.primitiveLeftActionComponent p p a).hom.hom
        ⟨y, hySocle, rfl⟩
  have hoffDiagonal (q : S.ProjectiveLabel) (hqp : q ≠ p) :
      P.idempotent q * (a * y.1) = 0 := by
    let z : MagnitudeConjecture.moduleSocleFGObj
        (RightModule.rightIdealFGObj (P.idempotent p)) :=
      ⟨y, hySocle⟩
    have hzero := congrArg
      (fun f : MagnitudeConjecture.moduleSocleFGObj
          (RightModule.rightIdealFGObj (P.idempotent p)) ⟶
            RightModule.rightIdealFGObj (P.idempotent q) ↦
        f.hom.hom z)
      (P.moduleSocleInclusion_comp_primitiveLeftActionComponent_eq_zero
        p q hpInjective hqp a)
    have hvalue :
        (P.primitiveLeftActionComponent p q a).hom.hom y = 0 := by
      simpa [z] using hzero
    have hvalueVal := congrArg Subtype.val hvalue
    rw [P.primitiveLeftActionComponent_apply_val] at hvalueVal
    have hzeroVal :
        ((0 : RightModule.rightIdealFGObj (P.idempotent q)) :
          RightModule.rightIdeal (P.idempotent q)).1 = 0 := rfl
    exact hvalueVal.trans hzeroVal
  have hsum :
      (∑ q : S.ProjectiveLabel, P.idempotent q * (a * y.1)) =
        P.idempotent p * (a * y.1) := by
    apply Finset.sum_eq_single p
    · intro q _ hqp
      exact hoffDiagonal q hqp
    · simp
  have hleftAction :
      a * y.1 = P.idempotent p * (a * y.1) := by
    calc
      a * y.1 = 1 * (a * y.1) := (one_mul _).symm
      _ = (∑ q : S.ProjectiveLabel, P.idempotent q) *
          (a * y.1) := by rw [P.complete.complete]
      _ = ∑ q : S.ProjectiveLabel,
          P.idempotent q * (a * y.1) := by rw [Finset.sum_mul]
      _ = P.idempotent p * (a * y.1) := hsum
  change a * x ∈ P.primitiveProjectiveSocleSubmodule p
  rw [primitiveProjectiveSocleSubmodule, Submodule.mem_map]
  refine ⟨(P.primitiveLeftActionComponent p p a).hom.hom y,
    hdiagonalSocle, ?_⟩
  change
    ((P.primitiveLeftActionComponent p p a).hom.hom y).1 = a * x
  calc
    ((P.primitiveLeftActionComponent p p a).hom.hom y).1 =
        P.idempotent p * (a * y.1) :=
      P.primitiveLeftActionComponent_apply_val p p a y
    _ = a * y.1 := hleftAction.symm
    _ = a * x := congrArg (fun z ↦ a * z) hyx

/-- The socle of a selected primitive projective-injective, embedded in the
regular module, is a two-sided ideal. -/
def primitiveProjectiveSocleIdeal
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label)) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk'
    (P.primitiveProjectiveSocleSubmodule p)
    (P.primitiveProjectiveSocleSubmodule p).zero_mem
    (fun hx hy ↦ (P.primitiveProjectiveSocleSubmodule p).add_mem hx hy)
    (fun hx ↦ (P.primitiveProjectiveSocleSubmodule p).neg_mem hx)
    (fun hx ↦ P.mul_mem_primitiveProjectiveSocleSubmodule p hpInjective hx)
    (fun {x y} hx ↦ by
      change (MulOpposite.op y) • x ∈
        P.primitiveProjectiveSocleSubmodule p
      exact (P.primitiveProjectiveSocleSubmodule p).smul_mem
        (MulOpposite.op y) hx)

@[simp]
theorem mem_primitiveProjectiveSocleIdeal
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (x : A) :
    x ∈ P.primitiveProjectiveSocleIdeal p hpInjective ↔
      x ∈ P.primitiveProjectiveSocleSubmodule p := by
  simp [primitiveProjectiveSocleIdeal]

/-- Every indecomposable module other than the selected
projective-injective is annihilated by its embedded socle ideal. -/
theorem isAnnihilatedBy_primitiveProjectiveSocleIdeal_of_not_iso
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (M : RightModule.FinitelyGeneratedCategory A)
    (hM : Indecomposable M)
    (hnoniso : ¬ Nonempty (M ≅ S.fgObj p.label)) :
    RightModule.IsAnnihilatedBy
      (P.primitiveProjectiveSocleIdeal p hpInjective) M := by
  let pIso := P.primitiveProjectiveIso p
  letI : Injective
      (RightModule.rightIdealFGObj (P.idempotent p)) :=
    Injective.of_iso pIso.symm hpInjective
  let hPind : Indecomposable
      (RightModule.rightIdealFGObj (P.idempotent p)) :=
    RightModule.rightIdealFGObj_indecomposable (P.primitive p)
  have hnonisoLiteral : ¬ Nonempty
      (RightModule.rightIdealFGObj (P.idempotent p) ≅ M) := by
    rintro ⟨e⟩
    exact hnoniso ⟨e.symm ≪≫ pIso⟩
  intro x a ha
  have haSubmodule :
      a ∈ P.primitiveProjectiveSocleSubmodule p :=
    (P.mem_primitiveProjectiveSocleIdeal p hpInjective a).1 ha
  change a ∈
    (moduleSocle Aᵐᵒᵖ
      (RightModule.rightIdealFGObj (P.idempotent p))).map
        (RightModule.rightIdeal (P.idempotent p)).subtype at haSubmodule
  obtain ⟨y, hySocle, hya⟩ := (Submodule.mem_map).1 haSubmodule
  let f : RightModule.rightIdealFGObj (P.idempotent p) ⟶ M :=
    RightModule.rightIdealActionHom (P.idempotent p) M x
  have hkill :
      MagnitudeConjecture.moduleSocleInclusion
          (RightModule.rightIdealFGObj (P.idempotent p)) ≫ f = 0 :=
    MagnitudeConjecture.moduleSocleInclusion_comp_eq_zero_of_not_iso
      (k := k) _ M hPind hM hnonisoLiteral f
  let z : MagnitudeConjecture.moduleSocleFGObj
      (RightModule.rightIdealFGObj (P.idempotent p)) :=
    ⟨y, hySocle⟩
  have hvalue := congrArg
    (fun g : MagnitudeConjecture.moduleSocleFGObj
        (RightModule.rightIdealFGObj (P.idempotent p)) ⟶ M ↦
      g.hom.hom z) hkill
  have hyzero : (MulOpposite.op y.1) • x = 0 := by
    simpa [f, z] using hvalue
  rw [← hya]
  exact hyzero

/-- In the fixed finite skeleton, every label except the rejected
projective-injective belongs to the annihilated quotient subcategory. -/
theorem fgObj_isAnnihilatedBy_primitiveProjectiveSocleIdeal
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (i : Fin S.n) (hip : i ≠ p.label) :
    RightModule.IsAnnihilatedBy
      (P.primitiveProjectiveSocleIdeal p hpInjective) (S.fgObj i) := by
  apply P.isAnnihilatedBy_primitiveProjectiveSocleIdeal_of_not_iso
    p hpInjective (S.fgObj i) (S.fgObj_indecomposable i)
  rintro ⟨e⟩
  exact hip (S.fgObj_skeletal ⟨e⟩)

/-- The rejected literal primitive projective is not annihilated by its own
socle ideal. -/
theorem rightIdealFGObj_not_isAnnihilatedBy_primitiveProjectiveSocleIdeal
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label)) :
    ¬ RightModule.IsAnnihilatedBy
      (P.primitiveProjectiveSocleIdeal p hpInjective)
        (RightModule.rightIdealFGObj (P.idempotent p)) := by
  let pIso : RightModule.rightIdealFGObj (P.idempotent p) ≅
      S.fgObj p.label :=
    (S.primitiveSourceIso (P.primitive p)).trans
      (eqToIso (congrArg S.fgObj
        (congrArg ProjectiveLabel.label (P.sourceLabel p))))
  letI : Injective
      (RightModule.rightIdealFGObj (P.idempotent p)) :=
    Injective.of_iso pIso.symm hpInjective
  let hPind : Indecomposable
      (RightModule.rightIdealFGObj (P.idempotent p)) :=
    RightModule.rightIdealFGObj_indecomposable (P.primitive p)
  have hsocleSimple : IsSimpleModule Aᵐᵒᵖ
      (moduleSocle Aᵐᵒᵖ
        (RightModule.rightIdealFGObj (P.idempotent p))) :=
    MagnitudeConjecture.moduleSocle_isSimple_of_injective_indecomposable
      (k := k) _ hPind
  letI : Nontrivial
      (moduleSocle Aᵐᵒᵖ
        (RightModule.rightIdealFGObj (P.idempotent p))) :=
    hsocleSimple.nontrivial
  obtain ⟨z, hz⟩ := exists_ne
    (0 : moduleSocle Aᵐᵒᵖ
      (RightModule.rightIdealFGObj (P.idempotent p)))
  have hzIdeal : z.1.1 ∈
      P.primitiveProjectiveSocleIdeal p hpInjective := by
    rw [P.mem_primitiveProjectiveSocleIdeal]
    change z.1.1 ∈
      (moduleSocle Aᵐᵒᵖ
        (RightModule.rightIdealFGObj (P.idempotent p))).map
          (RightModule.rightIdeal (P.idempotent p)).subtype
    exact ⟨z.1, z.2, rfl⟩
  intro hann
  have hzero := hann (RightModule.rightIdealGenerator (P.idempotent p))
    z.1.1 hzIdeal
  have hzeroVal := congrArg Subtype.val hzero
  have hfixed := RightModule.rightIdeal_fixed
    (P.primitive p).idempotent z.1
  apply hz
  apply Subtype.ext
  apply Subtype.ext
  exact hfixed.symm.trans hzeroVal

/-- The selected skeletal projective is not annihilated by its own socle
ideal. -/
theorem fgObj_not_isAnnihilatedBy_primitiveProjectiveSocleIdeal
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label)) :
    ¬ RightModule.IsAnnihilatedBy
      (P.primitiveProjectiveSocleIdeal p hpInjective) (S.fgObj p.label) := by
  let pIso : RightModule.rightIdealFGObj (P.idempotent p) ≅
      S.fgObj p.label :=
    (S.primitiveSourceIso (P.primitive p)).trans
      (eqToIso (congrArg S.fgObj
        (congrArg ProjectiveLabel.label (P.sourceLabel p))))
  intro hann
  apply P.rightIdealFGObj_not_isAnnihilatedBy_primitiveProjectiveSocleIdeal
    p hpInjective
  intro x a ha
  have hzero := hann (pIso.hom.hom x) a ha
  have hback := congrArg pIso.inv.hom.hom hzero
  rw [map_smul, map_zero] at hback
  have hinv := congrArg
    (fun f : RightModule.rightIdealFGObj (P.idempotent p) ⟶
        RightModule.rightIdealFGObj (P.idempotent p) ↦ f.hom.hom x)
    pIso.hom_inv_id
  change pIso.inv.hom.hom (pIso.hom.hom x) = x at hinv
  rw [hinv] at hback
  exact hback

/-- The annihilated indecomposable labels are exactly the complement of the
rejected projective-injective label. -/
theorem fgObj_isAnnihilatedBy_primitiveProjectiveSocleIdeal_iff
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (i : Fin S.n) :
    RightModule.IsAnnihilatedBy
        (P.primitiveProjectiveSocleIdeal p hpInjective) (S.fgObj i) ↔
      i ≠ p.label := by
  constructor
  · intro hi hip
    subst i
    exact
      (P.fgObj_not_isAnnihilatedBy_primitiveProjectiveSocleIdeal
        p hpInjective) hi
  · exact P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleIdeal
      p hpInjective i

/-- The quotient's intrinsic label type is canonically the complement of the
single rejected ambient label. -/
def socleQuotientLabelEquivComplement
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label)) :
    S.IdealQuotientLabel
        (P.primitiveProjectiveSocleIdeal p hpInjective) ≃
      {i : Fin S.n // i ≠ p.label} where
  toFun i :=
    ⟨i.1,
      (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleIdeal_iff
        p hpInjective i.1).1 i.2⟩
  invFun i :=
    ⟨i.1,
      (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleIdeal_iff
        p hpInjective i.1).2 i.2⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl

/-- One socle rejection removes exactly one indecomposable label. -/
theorem card_socleQuotientLabel_add_one
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label)) :
    Fintype.card
        (S.IdealQuotientLabel
          (P.primitiveProjectiveSocleIdeal p hpInjective)) + 1 =
      S.n := by
  classical
  rw [Fintype.card_congr
    (P.socleQuotientLabelEquivComplement p hpInjective)]
  have hcard := Fintype.card_congr (Equiv.optionSubtypeNe p.label)
  simpa using hcard

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
