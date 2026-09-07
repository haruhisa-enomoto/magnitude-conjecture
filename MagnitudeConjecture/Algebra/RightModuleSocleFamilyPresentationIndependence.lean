import MagnitudeConjecture.Algebra.RightModuleMoritaBasicUniqueness
import MagnitudeConjecture.Algebra.RightModuleProjectiveInjectiveSocleFamily

/-!
# Independence of primitive-projective socle families

Two complete primitive-projective presentations of the same duplicate-free
right-module skeleton determine the same embedded socle ideal at each
injective projective label, and hence the same simultaneous family ideal.

The proof compares the two decompositions of the regular right module.  The
resulting regular-module automorphism matches corresponding projective
summands and their socles.  Since an endomorphism of the regular right module
is left multiplication by its value at one, two-sidedness turns that transported
equality back into literal equality inside the ambient algebra.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton.PrimitiveProjectivePresentation

universe u

variable {k A : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

def regularChangeIso
    (P Q : S.PrimitiveProjectivePresentation) :
    RightModule.rightRegularFGObj (B := A) ≅
      RightModule.rightRegularFGObj (B := A) :=
  P.regularIsoBasicProjectiveGenerator.trans
    Q.regularIsoBasicProjectiveGenerator.symm

theorem rightIdealInclusion_comp_regularDecompositionMap
    (P : S.PrimitiveProjectivePresentation)
    (p : S.ProjectiveLabel) :
    RightModule.rightIdealInclusion (P.idempotent p) ≫
        RightModule.regularDecompositionMap P.idempotent =
      biproduct.ι
        (fun q : S.ProjectiveLabel ↦
          RightModule.rightIdealFGObj (P.idempotent q)) p := by
  apply biproduct.hom_ext
  intro q
  simp only [Category.assoc, RightModule.regularDecompositionMap,
    biproduct.lift_π]
  by_cases hpq : p = q
  · subst q
    rw [biproduct.ι_π_self]
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact RightModule.rightIdeal_fixed (P.complete.idem p) x
  · rw [biproduct.ι_π_ne _ hpq]
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    obtain ⟨a, ha⟩ := x.2
    change P.idempotent q * x.1 = 0
    change P.idempotent p * a = x.1 at ha
    rw [← ha, ← mul_assoc, P.complete.ortho (Ne.symm hpq), zero_mul]

theorem rightIdealInclusion_comp_regularChangeIso_hom
    (P Q : S.PrimitiveProjectivePresentation)
    (p : S.ProjectiveLabel) :
    RightModule.rightIdealInclusion (P.idempotent p) ≫
        (regularChangeIso P Q).hom =
      (P.primitiveProjectiveIso p).hom ≫
        (Q.primitiveProjectiveIso p).inv ≫
        RightModule.rightIdealInclusion (Q.idempotent p) := by
  change
    RightModule.rightIdealInclusion (P.idempotent p) ≫
          ((RightModule.regularDecompositionIso P.idempotent P.complete).hom ≫
            (biproduct.mapIso fun p ↦ P.primitiveProjectiveIso p).hom) ≫
        ((biproduct.mapIso fun p ↦ Q.primitiveProjectiveIso p).inv ≫
          (RightModule.regularDecompositionIso Q.idempotent Q.complete).inv) = _
  simp only [← Category.assoc]
  rw [RightModule.regularDecompositionIso,
    rightIdealInclusion_comp_regularDecompositionMap]
  simp
  change
    biproduct.ι
        (fun q : S.ProjectiveLabel ↦
          RightModule.rightIdealFGObj (Q.idempotent q)) p ≫
        RightModule.regularAssemblyMap Q.idempotent =
      RightModule.rightIdealInclusion (Q.idempotent p)
  simp [RightModule.regularAssemblyMap]

def primitiveProjectiveChangeIso
    (P Q : S.PrimitiveProjectivePresentation)
    (p : S.ProjectiveLabel) :
    RightModule.rightIdealFGObj (P.idempotent p) ≅
      RightModule.rightIdealFGObj (Q.idempotent p) :=
  (P.primitiveProjectiveIso p).trans
    (Q.primitiveProjectiveIso p).symm

theorem map_primitiveProjectiveSocleSubmodule_regularChangeIso
    (P Q : S.PrimitiveProjectivePresentation)
    (p : S.ProjectiveLabel) :
    (P.primitiveProjectiveSocleSubmodule p).map
        (regularChangeIso P Q).hom.hom.hom =
      Q.primitiveProjectiveSocleSubmodule p := by
  let e := FGModuleCat.isoToLinearEquiv (primitiveProjectiveChangeIso P Q p)
  have hsocle :
      (moduleSocle Aᵐᵒᵖ
        (RightModule.rightIdealFGObj (P.idempotent p))).map e.toLinearMap =
      moduleSocle Aᵐᵒᵖ
        (RightModule.rightIdealFGObj (Q.idempotent p)) :=
    map_moduleSocle_eq_of_linearEquiv e
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x ∈
      (moduleSocle Aᵐᵒᵖ
        (RightModule.rightIdealFGObj (P.idempotent p))).map
          (RightModule.rightIdeal (P.idempotent p)).subtype at hx
    obtain ⟨z, hz, rfl⟩ := (Submodule.mem_map).1 hx
    let z' := e z
    have hz' : z' ∈ moduleSocle Aᵐᵒᵖ
        (RightModule.rightIdealFGObj (Q.idempotent p)) := by
      rw [← hsocle]
      exact ⟨z, hz, rfl⟩
    change (regularChangeIso P Q).hom.hom.hom z.1 ∈
      (moduleSocle Aᵐᵒᵖ
        (RightModule.rightIdealFGObj (Q.idempotent p))).map
          (RightModule.rightIdeal (Q.idempotent p)).subtype
    refine ⟨z', hz', ?_⟩
    have hcomp := rightIdealInclusion_comp_regularChangeIso_hom P Q p
    have hvalue := congrArg
      (fun f : RightModule.rightIdealFGObj (P.idempotent p) ⟶
          RightModule.rightRegularFGObj (B := A) ↦ f.hom.hom z) hcomp
    change
      (((P.primitiveProjectiveIso p).hom ≫
        (Q.primitiveProjectiveIso p).inv).hom.hom z).1 =
          (regularChangeIso P Q).hom.hom.hom z.1
    exact hvalue.symm
  · intro hy
    change y ∈
      (moduleSocle Aᵐᵒᵖ
        (RightModule.rightIdealFGObj (Q.idempotent p))).map
          (RightModule.rightIdeal (Q.idempotent p)).subtype at hy
    obtain ⟨z, hz, rfl⟩ := (Submodule.mem_map).1 hy
    let w := e.symm z
    have hsocleInv :
        (moduleSocle Aᵐᵒᵖ
          (RightModule.rightIdealFGObj (Q.idempotent p))).map
            e.symm.toLinearMap =
          moduleSocle Aᵐᵒᵖ
            (RightModule.rightIdealFGObj (P.idempotent p)) :=
      map_moduleSocle_eq_of_linearEquiv e.symm
    have hw : w ∈ moduleSocle Aᵐᵒᵖ
        (RightModule.rightIdealFGObj (P.idempotent p)) := by
      rw [← hsocleInv]
      exact ⟨z, hz, rfl⟩
    refine ⟨w.1, ?_, ?_⟩
    · change w.1 ∈
        (moduleSocle Aᵐᵒᵖ
          (RightModule.rightIdealFGObj (P.idempotent p))).map
            (RightModule.rightIdeal (P.idempotent p)).subtype
      exact ⟨w, hw, rfl⟩
    · have hcomp := rightIdealInclusion_comp_regularChangeIso_hom P Q p
      have hvalue := congrArg
        (fun f : RightModule.rightIdealFGObj (P.idempotent p) ⟶
            RightModule.rightRegularFGObj (B := A) ↦ f.hom.hom w) hcomp
      have hew : e w = z := e.apply_symm_apply z
      exact hvalue.trans (congrArg
        (fun q : RightModule.rightIdealFGObj (Q.idempotent p) ↦ q.1) hew)

omit [IsNoetherianRing Aᵐᵒᵖ] in
theorem rightRegularFGHom_apply_eq_apply_one_mul
    (f : RightModule.rightRegularFGObj (B := A) ⟶
      RightModule.rightRegularFGObj (B := A)) (x : A) :
    f.hom.hom x = f.hom.hom 1 * x := by
  have hx := f.hom.hom.map_smul (MulOpposite.op x) (1 : A)
  simpa using hx

theorem primitiveProjectiveSocleIdeal_le_of_presentations
    (P Q : S.PrimitiveProjectivePresentation)
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label)) :
    P.primitiveProjectiveSocleIdeal p hpInjective ≤
      Q.primitiveProjectiveSocleIdeal p hpInjective := by
  intro x hx
  have hxSubmodule :=
    (P.mem_primitiveProjectiveSocleIdeal p hpInjective x).1 hx
  let g := regularChangeIso P Q
  have hgx : g.hom.hom.hom x ∈
      Q.primitiveProjectiveSocleSubmodule p := by
    rw [← map_primitiveProjectiveSocleSubmodule_regularChangeIso P Q p]
    exact ⟨x, hxSubmodule, rfl⟩
  have hgxIdeal : g.hom.hom.hom x ∈
      Q.primitiveProjectiveSocleIdeal p hpInjective :=
    (Q.mem_primitiveProjectiveSocleIdeal p hpInjective _).2 hgx
  have hinvMem : g.inv.hom.hom 1 * g.hom.hom.hom x ∈
      Q.primitiveProjectiveSocleIdeal p hpInjective :=
    (Q.primitiveProjectiveSocleIdeal p hpInjective).mul_mem_left _ _ hgxIdeal
  have hinvApply :
      g.inv.hom.hom (g.hom.hom.hom x) =
        g.inv.hom.hom 1 * g.hom.hom.hom x :=
    rightRegularFGHom_apply_eq_apply_one_mul g.inv (g.hom.hom.hom x)
  have hback : g.inv.hom.hom (g.hom.hom.hom x) = x := by
    have h := congrArg
      (fun f : RightModule.rightRegularFGObj (B := A) ⟶
          RightModule.rightRegularFGObj (B := A) ↦ f.hom.hom x)
      g.hom_inv_id
    change g.inv.hom.hom (g.hom.hom.hom x) = x at h
    exact h
  rwa [← hinvApply, hback] at hinvMem

theorem primitiveProjectiveSocleIdeal_eq_of_presentations
    (P Q : S.PrimitiveProjectivePresentation)
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label)) :
    P.primitiveProjectiveSocleIdeal p hpInjective =
      Q.primitiveProjectiveSocleIdeal p hpInjective :=
  le_antisymm
    (primitiveProjectiveSocleIdeal_le_of_presentations P Q p hpInjective)
    (primitiveProjectiveSocleIdeal_le_of_presentations Q P p hpInjective)

theorem primitiveProjectiveSocleFamilyIdeal_eq_of_presentations
    (P Q : S.PrimitiveProjectivePresentation)
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label)) :
    P.primitiveProjectiveSocleFamilyIdeal T hInjective =
      Q.primitiveProjectiveSocleFamilyIdeal T hInjective := by
  apply le_antisymm
  · apply iSup_le
    intro p
    rw [primitiveProjectiveSocleIdeal_eq_of_presentations P Q p.1
      (hInjective p.1 p.2)]
    exact le_iSup
      (fun q : {q // q ∈ T} ↦
        Q.primitiveProjectiveSocleIdeal q.1 (hInjective q.1 q.2)) p
  · apply iSup_le
    intro p
    rw [primitiveProjectiveSocleIdeal_eq_of_presentations Q P p.1
      (hInjective p.1 p.2)]
    exact le_iSup
      (fun q : {q // q ∈ T} ↦
        P.primitiveProjectiveSocleIdeal q.1 (hInjective q.1 q.2)) p

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton.PrimitiveProjectivePresentation
