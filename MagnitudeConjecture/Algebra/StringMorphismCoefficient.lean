import MagnitudeConjecture.Algebra.StringFiniteModule

/-!
# Position coefficients of morphisms between string modules

A displayed arrow acts as a partial bijection on the position basis of a
string word.  This file turns naturality of an arbitrary morphism between two
string modules into the local coefficient rules used in graph-map theory:
coefficients propagate across two matched arrow steps and vanish at an
unmatched source or target boundary.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- A string word has at most one source position mapping to a fixed target
position under a displayed arrow. -/
theorem arrowStep_source_subsingleton (C : Word R) {x y : Q}
    (a : x ⟶ y) (j : C.PositionAt y) :
    Subsingleton {i : C.PositionAt x // C.ArrowStep a i j} := by
  constructor
  rintro ⟨i, hi⟩ ⟨i', hi'⟩
  apply Subtype.ext
  rcases hi with hi | hi <;> rcases hi' with hi' | hi'
  · apply Subtype.ext
    exact Quiver.Path.comp_injective_left
      (positiveArrow a).toPath (hi.symm.trans hi')
  · exfalso
    let e := positiveArrow a
    apply C.isString.1 e
    rcases i'.2 with ⟨r, hr⟩
    refine ⟨i.1, r, ?_⟩
    calc
      C.path = i'.1.comp r := hr
      _ = (j.1.comp (negativeArrow a).toPath).comp r :=
        congrArg (fun p => p.comp r) hi'
      _ = ((i.1.comp (positiveArrow a).toPath).comp
          (negativeArrow a).toPath).comp r :=
        congrArg
          (fun p => (p.comp (negativeArrow a).toPath).comp r) hi
      _ = i.1.comp ((e.toPath.comp
          (Quiver.reverse e).toPath).comp r) := by
        simp only [e, reverse_positiveArrow, Quiver.Path.comp_assoc]
  · exfalso
    let e := positiveArrow a
    apply C.isString.1 e
    rcases i.2 with ⟨r, hr⟩
    refine ⟨i'.1, r, ?_⟩
    calc
      C.path = i.1.comp r := hr
      _ = (j.1.comp (negativeArrow a).toPath).comp r :=
        congrArg (fun p => p.comp r) hi
      _ = ((i'.1.comp (positiveArrow a).toPath).comp
          (negativeArrow a).toPath).comp r :=
        congrArg
          (fun p => (p.comp (negativeArrow a).toPath).comp r) hi'
      _ = i'.1.comp ((e.toPath.comp
          (Quiver.reverse e).toPath).comp r) := by
        simp only [e, reverse_positiveArrow, Quiver.Path.comp_assoc]
  · apply Subtype.ext
    exact hi.trans hi'.symm

/-- Away from a witnessed arrow step, the corresponding target coefficient
of the image basis vector is zero. -/
theorem arrowOnBasis_apply_eq_zero_of_not_step
    (C : Word R) {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) (j : C.PositionAt y)
    (hij : ¬ C.ArrowStep a i j) :
    C.arrowOnBasis a i j = 0 := by
  classical
  rw [arrowOnBasis]
  split_ifs with h
  · have hne : Classical.choose h ≠ j := by
      intro heq
      apply hij
      simpa [heq] using Classical.choose_spec h
    simp [hne]
  · rfl

/-- A displayed-arrow map reads the unique source coefficient at every
witnessed target position. -/
theorem arrowLinearMap_apply_of_step
    (C : Word R) {x y : Q} (a : x ⟶ y)
    (v : C.Space x) (i : C.PositionAt x) (j : C.PositionAt y)
    (hij : C.ArrowStep a i j) :
    C.arrowLinearMap a v j = v i := by
  classical
  let targetCoordinate : C.Space y →ₗ[k] k := Finsupp.lapply j
  let sourceCoordinate : C.Space x →ₗ[k] k := Finsupp.lapply i
  have hmaps : targetCoordinate.comp (C.arrowLinearMap a) =
      sourceCoordinate := by
    apply Finsupp.lhom_ext
    intro l c
    dsimp only [targetCoordinate, sourceCoordinate]
    rw [LinearMap.comp_apply, C.arrowLinearMap_single]
    change (c • C.arrowOnBasis a l) j = (Finsupp.single l c) i
    by_cases hli : l = i
    · subst l
      rw [C.arrowOnBasis_eq_single_of_step a i j hij]
      simp
    · have hnot : ¬ C.ArrowStep a l j := by
        intro hlj
        have hsources :
            (⟨l, hlj⟩ : {t : C.PositionAt x // C.ArrowStep a t j}) =
              ⟨i, hij⟩ :=
          @Subsingleton.elim _ (C.arrowStep_source_subsingleton a j) _ _
        exact hli (congrArg Subtype.val hsources)
      rw [Finsupp.smul_apply,
        C.arrowOnBasis_apply_eq_zero_of_not_step a l j hnot]
      simp [hli]
  exact LinearMap.congr_fun hmaps v

/-- If a target position has no source under a displayed arrow, every arrow
image has zero coefficient there. -/
theorem arrowLinearMap_apply_eq_zero_of_not_exists_source
    (C : Word R) {x y : Q} (a : x ⟶ y)
    (v : C.Space x) (j : C.PositionAt y)
    (hj : ¬ ∃ i : C.PositionAt x, C.ArrowStep a i j) :
    C.arrowLinearMap a v j = 0 := by
  classical
  let targetCoordinate : C.Space y →ₗ[k] k := Finsupp.lapply j
  have hmap : targetCoordinate.comp (C.arrowLinearMap a) = 0 := by
    apply Finsupp.lhom_ext
    intro i c
    dsimp only [targetCoordinate]
    rw [LinearMap.comp_apply, C.arrowLinearMap_single]
    change (c • C.arrowOnBasis a i) j = 0
    rw [Finsupp.smul_apply,
      C.arrowOnBasis_apply_eq_zero_of_not_step a i j
        (fun hij => hj ⟨i, hij⟩)]
    simp
  have hvalue := LinearMap.congr_fun hmap v
  exact hvalue

/-- The coefficient from a source position basis vector to a target position
basis vector for a morphism between two string modules. -/
def morphismCoefficient
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    {x : Q} (i : C.PositionAt x) (j : D.PositionAt x) : k :=
  (show D.Space x from
    (f.app (Opposite.op (obj R x))).hom (Finsupp.single i 1)) j

/-- A morphism coefficient propagates across a pair of matched displayed-arrow
steps in the source and target strings. -/
theorem morphismCoefficient_eq_of_arrowSteps
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) (j : C.PositionAt y)
    (i' : D.PositionAt x) (j' : D.PositionAt y)
    (hij : C.ArrowStep a i j) (hij' : D.ArrowStep a i' j') :
    C.morphismCoefficient D hC hD f i i' =
      C.morphismCoefficient D hC hD f j j' := by
  have happ := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom
      (f.naturality (pathMap R a.toPath).op))
    (Finsupp.single i 1)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    C.rightModule_map_pathMap hC a.toPath,
    D.rightModule_map_pathMap hD a.toPath] at happ
  let fx : C.Space x →ₗ[k] D.Space x :=
    (f.app (Opposite.op (obj R x))).hom
  let fy : C.Space y →ₗ[k] D.Space y :=
    (f.app (Opposite.op (obj R y))).hom
  change
    fy (C.arrowLinearMap a (Finsupp.single i 1)) =
      D.arrowLinearMap a (fx (Finsupp.single i 1)) at happ
  have hcoeff := congrArg (fun v : D.Space y => v j') happ
  rw [C.arrowLinearMap_single_one_of_step a i j hij,
    D.arrowLinearMap_apply_of_step a _ i' j' hij'] at hcoeff
  exact hcoeff.symm

/-- A coefficient vanishes at a target-string boundary when the source-string
basis vector crosses the displayed arrow but the target position has no
incoming matched step. -/
theorem morphismCoefficient_eq_zero_of_source_step_of_no_target_source
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) (j : C.PositionAt y)
    (j' : D.PositionAt y)
    (hij : C.ArrowStep a i j)
    (hj' : ¬ ∃ i' : D.PositionAt x, D.ArrowStep a i' j') :
    C.morphismCoefficient D hC hD f j j' = 0 := by
  have happ := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom
      (f.naturality (pathMap R a.toPath).op))
    (Finsupp.single i 1)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    C.rightModule_map_pathMap hC a.toPath,
    D.rightModule_map_pathMap hD a.toPath] at happ
  let fx : C.Space x →ₗ[k] D.Space x :=
    (f.app (Opposite.op (obj R x))).hom
  let fy : C.Space y →ₗ[k] D.Space y :=
    (f.app (Opposite.op (obj R y))).hom
  change
    fy (C.arrowLinearMap a (Finsupp.single i 1)) =
      D.arrowLinearMap a (fx (Finsupp.single i 1)) at happ
  have hcoeff := congrArg (fun v : D.Space y => v j') happ
  rw [C.arrowLinearMap_single_one_of_step a i j hij,
    D.arrowLinearMap_apply_eq_zero_of_not_exists_source a _ j' hj'] at hcoeff
  exact hcoeff

/-- A coefficient vanishes at a source-string boundary when its source basis
vector has no outgoing displayed-arrow step but the target position does. -/
theorem morphismCoefficient_eq_zero_of_no_source_target_of_target_step
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) (i' : D.PositionAt x) (j' : D.PositionAt y)
    (hi : ¬ ∃ j : C.PositionAt y, C.ArrowStep a i j)
    (hij' : D.ArrowStep a i' j') :
    C.morphismCoefficient D hC hD f i i' = 0 := by
  have happ := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom
      (f.naturality (pathMap R a.toPath).op))
    (Finsupp.single i 1)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    C.rightModule_map_pathMap hC a.toPath,
    D.rightModule_map_pathMap hD a.toPath] at happ
  let fx : C.Space x →ₗ[k] D.Space x :=
    (f.app (Opposite.op (obj R x))).hom
  let fy : C.Space y →ₗ[k] D.Space y :=
    (f.app (Opposite.op (obj R y))).hom
  change
    fy (C.arrowLinearMap a (Finsupp.single i 1)) =
      D.arrowLinearMap a (fx (Finsupp.single i 1)) at happ
  have hcoeff := congrArg (fun v : D.Space y => v j') happ
  rw [C.arrowLinearMap_single, one_smul,
    C.arrowOnBasis_eq_zero_of_not_exists a i hi, map_zero,
    Finsupp.zero_apply,
    D.arrowLinearMap_apply_of_step a _ i' j' hij'] at hcoeff
  change fx (Finsupp.single i 1) i' = 0
  exact hcoeff.symm

end MagnitudeConjecture.BoundQuiver.StringWord.Word
