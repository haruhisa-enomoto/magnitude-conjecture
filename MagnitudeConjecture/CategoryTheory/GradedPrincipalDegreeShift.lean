import MagnitudeConjecture.CategoryTheory.GradedProjectiveCornerCategory

/-! # Translation of the degree-labelled principal-projective category -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type} [Fintype ι] (e : ι → A)
variable (he0 : ∀ i, e i ∈ R.component 0) (he : ∀ i, e i * e i = e i)

/-- Simultaneous degree translation leaves the corner coefficient unchanged. -/
def principalDegreeShiftMap (t : ℤ) {p q : PrincipalDegreeCategory R hmul e he0}
    (f : p ⟶ q) :
    (show PrincipalDegreeCategory R hmul e he0 from (p.1, p.2 + t)) ⟶
      (show PrincipalDegreeCategory R hmul e he0 from (q.1, q.2 + t)) :=
  (principalDegreeHomEquiv R hmul e he0 he _ _).symm
    ⟨(principalDegreeHomEquiv R hmul e he0 he p q f).val, by
      simpa using (principalDegreeHomEquiv R hmul e he0 he p q f).property⟩

@[simp]
theorem principalDegreeShiftMap_coeff (t : ℤ) {p q : PrincipalDegreeCategory R hmul e he0}
    (f : p ⟶ q) :
    (principalDegreeHomEquiv R hmul e he0 he _ _
      (principalDegreeShiftMap R hmul e he0 he t f)).val =
        (principalDegreeHomEquiv R hmul e he0 he p q f).val := by
  simp [principalDegreeShiftMap]

/-- Translation is a functor on degree-labelled principal projectives. -/
def principalDegreeShift (t : ℤ) :
    PrincipalDegreeCategory R hmul e he0 ⥤ PrincipalDegreeCategory R hmul e he0 where
  obj p := (p.1, p.2 + t)
  map f := principalDegreeShiftMap R hmul e he0 he t f
  map_id p := by
    apply (principalDegreeHomEquiv R hmul e he0 he _ _).injective
    apply Subtype.ext
    exact (principalDegreeShiftMap_coeff R hmul e he0 he t (𝟙 p)).trans
      ((principalDegreeHomEquiv_id R hmul e he0 he p).trans
        (principalDegreeHomEquiv_id R hmul e he0 he (p.1, p.2 + t)).symm)
  map_comp f g := by
    apply (principalDegreeHomEquiv R hmul e he0 he _ _).injective
    apply Subtype.ext
    exact (principalDegreeShiftMap_coeff R hmul e he0 he t (f ≫ g)).trans
      ((principalDegreeHomEquiv_comp R hmul e he0 he f g).trans
        ((congrArg₂ (· * ·)
          (principalDegreeShiftMap_coeff R hmul e he0 he t f).symm
          (principalDegreeShiftMap_coeff R hmul e he0 he t g).symm).trans
          (principalDegreeHomEquiv_comp R hmul e he0 he
            (principalDegreeShiftMap R hmul e he0 he t f)
            (principalDegreeShiftMap R hmul e he0 he t g)).symm))

instance principalDegreeShift_faithful (t : ℤ) :
    (principalDegreeShift R hmul e he0 he t).Faithful where
  map_injective {p q} f g hfg := by
    apply (principalDegreeHomEquiv R hmul e he0 he p q).injective
    apply Subtype.ext
    have hc := congrArg (fun f ↦ (principalDegreeHomEquiv R hmul e he0 he _ _ f).val) hfg
    exact (principalDegreeShiftMap_coeff R hmul e he0 he t f).symm.trans
      (hc.trans (principalDegreeShiftMap_coeff R hmul e he0 he t g))

instance principalDegreeShift_full (t : ℤ) :
    (principalDegreeShift R hmul e he0 he t).Full where
  map_surjective {p q} f := by
    let a := principalDegreeHomEquiv R hmul e he0 he _ _ f
    let g : p ⟶ q := (principalDegreeHomEquiv R hmul e he0 he p q).symm
      ⟨a.val, by simpa [a, principalDegreeShift] using a.property⟩
    refine ⟨g, ?_⟩
    apply (principalDegreeHomEquiv R hmul e he0 he _ _).injective
    apply Subtype.ext
    change (principalDegreeHomEquiv R hmul e he0 he _ _
      (principalDegreeShiftMap R hmul e he0 he t g)).val = a.val
    exact (principalDegreeShiftMap_coeff R hmul e he0 he t g).trans
      (congrArg Subtype.val ((principalDegreeHomEquiv R hmul e he0 he p q).apply_symm_apply _))

instance principalDegreeShift_essSurj (t : ℤ) :
    (principalDegreeShift R hmul e he0 he t).EssSurj where
  mem_essImage p := by
    refine ⟨(p.1, p.2 - t), ⟨eqToIso ?_⟩⟩
    apply Prod.ext
    · rfl
    · change p.2 - t + t = p.2
      omega

instance principalDegreeShift_additive (t : ℤ) :
    (principalDegreeShift R hmul e he0 he t).Additive where
  map_add {p q} f g := by
    apply (principalDegreeHomEquiv R hmul e he0 he _ _).injective
    apply Subtype.ext
    have h₁ := congrArg Subtype.val ((principalDegreeHomEquiv R hmul e he0 he p q).map_add f g)
    have h₂ := congrArg Subtype.val ((principalDegreeHomEquiv R hmul e he0 he _ _).map_add
      (principalDegreeShiftMap R hmul e he0 he t f)
      (principalDegreeShiftMap R hmul e he0 he t g))
    exact (principalDegreeShiftMap_coeff R hmul e he0 he t (f + g)).trans
      (h₁.trans ((congrArg₂ (· + ·)
        (principalDegreeShiftMap_coeff R hmul e he0 he t f).symm
        (principalDegreeShiftMap_coeff R hmul e he0 he t g).symm).trans h₂.symm))

instance principalDegreeShift_linear (t : ℤ) :
    (principalDegreeShift R hmul e he0 he t).Linear k where
  map_smul {p q} f c := by
    apply (principalDegreeHomEquiv R hmul e he0 he _ _).injective
    apply Subtype.ext
    have h₁ := congrArg Subtype.val ((principalDegreeHomEquiv R hmul e he0 he p q).map_smul c f)
    have h₂ := congrArg Subtype.val ((principalDegreeHomEquiv R hmul e he0 he _ _).map_smul c
      (principalDegreeShiftMap R hmul e he0 he t f))
    exact (principalDegreeShiftMap_coeff R hmul e he0 he t (c • f)).trans
      (h₁.trans ((congrArg (c • ·)
        (principalDegreeShiftMap_coeff R hmul e he0 he t f).symm).trans h₂.symm))

/-- Every common degree translation is an equivalence. -/
def principalDegreeShiftEquivalence (t : ℤ) :
    PrincipalDegreeCategory R hmul e he0 ≌ PrincipalDegreeCategory R hmul e he0 := by
  letI : (principalDegreeShift R hmul e he0 he t).IsEquivalence := {}
  exact (principalDegreeShift R hmul e he0 he t).asEquivalence

end MagnitudeConjecture.Graded.FiniteGradedModule
