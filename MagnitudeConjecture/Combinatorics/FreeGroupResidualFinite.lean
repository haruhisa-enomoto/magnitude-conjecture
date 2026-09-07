import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Mathlib.GroupTheory.ResiduallyFinite
import Mathlib.Logic.Equiv.Fintype

/-!
# Residual finiteness of free groups

The covering argument uses residual finiteness of its free deck group.  This
file supplies the missing Mathlib instance by the classical finite-path
construction.  A nonempty reduced word of length `n` determines partial
permutations of the `n + 1` path vertices, one for each generator.  Reducedness
makes both endpoint maps injective, so each partial permutation extends to a
permutation of the whole finite path.  The resulting free-group homomorphism
sends one endpoint to the other and therefore detects the word.
-/

set_option autoImplicit false

namespace MagnitudeConjecture

universe u

variable {α : Type u}

private def Occurrence (L : List (α × Bool)) (a : α) :=
  {i : Fin L.length // (L.get i).1 = a}

private noncomputable instance occurrenceFinite (L : List (α × Bool)) (a : α) :
    Finite (Occurrence L a) :=
  Finite.of_injective Subtype.val Subtype.val_injective

private def edgeStart (L : List (α × Bool)) (i : Fin L.length) :
    Fin (L.length + 1) :=
  Fin.rev i.succ

private def edgeEnd (L : List (α × Bool)) (i : Fin L.length) :
    Fin (L.length + 1) :=
  Fin.rev i.castSucc

private def occurrenceFrom (L : List (α × Bool)) (a : α) :
    Occurrence L a → Fin (L.length + 1) := fun i ↦
  if (L.get i.1).2 then edgeStart L i.1 else edgeEnd L i.1

private def occurrenceTo (L : List (α × Bool)) (a : α) :
    Occurrence L a → Fin (L.length + 1) := fun i ↦
  if (L.get i.1).2 then edgeEnd L i.1 else edgeStart L i.1

private theorem reduced_adjacent_sign_eq
    {L : List (α × Bool)} (hred : FreeGroup.IsReduced L)
    (i : Fin L.length) (hi : i.1 + 1 < L.length)
    (hgen : (L.get i).1 = (L.get ⟨i.1 + 1, hi⟩).1) :
    (L.get i).2 = (L.get ⟨i.1 + 1, hi⟩).2 := by
  unfold FreeGroup.IsReduced at hred
  rw [List.isChain_iff_getElem] at hred
  simpa only [List.get_eq_getElem] using hred i.1 hi hgen

private theorem reduced_sign_eq_of_succ
    {L : List (α × Bool)} (hred : FreeGroup.IsReduced L)
    {i j : Fin L.length} (hij : i.1 + 1 = j.1)
    (hgen : (L.get i).1 = (L.get j).1) :
    (L.get i).2 = (L.get j).2 := by
  have hi : i.1 + 1 < L.length := hij.symm ▸ j.2
  have hindex : (⟨i.1 + 1, hi⟩ : Fin L.length) = j := Fin.ext hij
  have hgen' : (L.get i).1 = (L.get ⟨i.1 + 1, hi⟩).1 := by
    simpa only [hindex] using hgen
  have hsign := reduced_adjacent_sign_eq hred i hi hgen'
  simpa only [hindex] using hsign

private theorem occurrenceFrom_injective
    {L : List (α × Bool)} (hred : FreeGroup.IsReduced L) (a : α) :
    Function.Injective (occurrenceFrom L a) := by
  intro i j hij
  apply Subtype.ext
  have hgen : (L.get i.1).1 = (L.get j.1).1 := i.2.trans j.2.symm
  by_cases hi : (L.get i.1).2
  · by_cases hj : (L.get j.1).2
    · simp only [occurrenceFrom, hi, hj, if_true, edgeStart] at hij
      exact Fin.succ_injective _ (Fin.rev_injective hij)
    · simp only [occurrenceFrom, hi, hj, if_true, edgeStart, edgeEnd] at hij
      have hadj : i.1.1 + 1 = j.1.1 := by
        have hij' := Fin.rev_injective hij
        exact congrArg Fin.val hij'
      have hsign := reduced_sign_eq_of_succ hred hadj hgen
      exact (hj (hsign.symm.trans hi)).elim
  · by_cases hj : (L.get j.1).2
    · simp only [occurrenceFrom, hi, hj, if_true, edgeStart, edgeEnd] at hij
      have hadj : j.1.1 + 1 = i.1.1 := by
        have hij' := Fin.rev_injective hij
        exact (congrArg Fin.val hij').symm
      have hsign := reduced_sign_eq_of_succ hred hadj hgen.symm
      exact (hi (hsign.symm.trans hj)).elim
    · simp only [occurrenceFrom, hi, hj, edgeEnd] at hij
      exact Fin.castSucc_injective _ (Fin.rev_injective hij)

private theorem occurrenceTo_injective
    {L : List (α × Bool)} (hred : FreeGroup.IsReduced L) (a : α) :
    Function.Injective (occurrenceTo L a) := by
  intro i j hij
  apply Subtype.ext
  have hgen : (L.get i.1).1 = (L.get j.1).1 := i.2.trans j.2.symm
  by_cases hi : (L.get i.1).2
  · by_cases hj : (L.get j.1).2
    · simp only [occurrenceTo, hi, hj, if_true, edgeEnd] at hij
      exact Fin.castSucc_injective _ (Fin.rev_injective hij)
    · simp only [occurrenceTo, hi, hj, if_true, edgeStart, edgeEnd] at hij
      have hadj : j.1.1 + 1 = i.1.1 := by
        have hij' := Fin.rev_injective hij
        exact (congrArg Fin.val hij').symm
      have hsign := reduced_sign_eq_of_succ hred hadj hgen.symm
      exact (hj (hsign.trans hi)).elim
  · by_cases hj : (L.get j.1).2
    · simp only [occurrenceTo, hi, hj, if_true, edgeStart, edgeEnd] at hij
      have hadj : i.1.1 + 1 = j.1.1 := by
        have hij' := Fin.rev_injective hij
        exact congrArg Fin.val hij'
      have hsign := reduced_sign_eq_of_succ hred hadj hgen
      exact (hi (hsign.trans hj)).elim
    · simp only [occurrenceTo, hi, hj, edgeStart] at hij
      exact Fin.succ_injective _ (Fin.rev_injective hij)

private noncomputable def generatorPerm
    {L : List (α × Bool)} (hred : FreeGroup.IsReduced L) (a : α) :
    Equiv.Perm (Fin (L.length + 1)) :=
  Classical.choose <| Equiv.Perm.exists_extending_pair
    (occurrenceFrom L a) (occurrenceTo L a)
    (occurrenceFrom_injective hred a) (occurrenceTo_injective hred a)

private theorem generatorPerm_apply
    {L : List (α × Bool)} (hred : FreeGroup.IsReduced L) (a : α)
    (i : Occurrence L a) :
    generatorPerm hred a (occurrenceFrom L a i) = occurrenceTo L a i :=
  Classical.choose_spec (Equiv.Perm.exists_extending_pair
    (occurrenceFrom L a) (occurrenceTo L a)
    (occurrenceFrom_injective hred a) (occurrenceTo_injective hred a)) i

private theorem letterPerm_moves_edge
    {L : List (α × Bool)} (hred : FreeGroup.IsReduced L) (i : Fin L.length) :
    (cond (L.get i).2
      (generatorPerm hred (L.get i).1)
      (generatorPerm hred (L.get i).1)⁻¹) (edgeStart L i) = edgeEnd L i := by
  cases hi : (L.get i).2 with
  | false =>
    have happly := generatorPerm_apply hred (L.get i).1
      (⟨i, rfl⟩ : Occurrence L (L.get i).1)
    have hinv := congrArg (generatorPerm hred (L.get i).1).symm happly
    simpa only [hi, cond_false, occurrenceFrom, occurrenceTo,
      Bool.false_eq_true, if_false, Equiv.Perm.coe_inv,
      Equiv.symm_apply_apply] using hinv.symm
  | true =>
    have happly := generatorPerm_apply hred (L.get i).1
      (⟨i, rfl⟩ : Occurrence L (L.get i).1)
    simpa only [hi, cond_true, occurrenceFrom, occurrenceTo,
      Bool.true_eq, if_true] using happly

private theorem perm_prod_moves_path
    {β : Type*} (fs : List (Equiv.Perm β))
    (x : Fin (fs.length + 1) → β)
    (hstep : ∀ i : Fin fs.length, fs.get i (x i.succ) = x i.castSucc) :
    fs.prod (x (Fin.last fs.length)) = x 0 := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
      let y : Fin (fs.length + 1) → β := fun i ↦ x i.succ
      have htail : ∀ i : Fin fs.length, fs.get i (y i.succ) = y i.castSucc := by
        intro i
        simpa only [y, List.get_cons_succ', Fin.succ_castSucc] using hstep i.succ
      have hprod := ih y htail
      have hhead := hstep (0 : Fin (f :: fs).length)
      simp only [List.prod_cons]
      rw [show x (Fin.last (f :: fs).length) = y (Fin.last fs.length) by
        apply congrArg x
        apply Fin.ext
        rfl]
      rw [Equiv.Perm.mul_apply, hprod]
      simpa only [y, List.get_cons_zero, Fin.castSucc_zero] using hhead

private noncomputable def separatingHom
    {L : List (α × Bool)} (hred : FreeGroup.IsReduced L) :
    FreeGroup α →* Equiv.Perm (Fin (L.length + 1)) :=
  FreeGroup.lift (generatorPerm hred)

private theorem separatingHom_mk_moves_endpoints
    {L : List (α × Bool)} (hred : FreeGroup.IsReduced L) :
    separatingHom hred (FreeGroup.mk L) (0 : Fin (L.length + 1)) =
      Fin.last L.length := by
  let fs : List (Equiv.Perm (Fin (L.length + 1))) :=
    L.map fun z ↦ cond z.2 (generatorPerm hred z.1) (generatorPerm hred z.1)⁻¹
  let x : Fin (fs.length + 1) → Fin (L.length + 1) := fun i ↦
    Fin.rev (i.cast (by simp only [fs, List.length_map]))
  have hstep : ∀ i : Fin fs.length, fs.get i (x i.succ) = x i.castSucc := by
    intro i
    let j : Fin L.length := i.cast (by simp only [fs, List.length_map])
    have hmove := letterPerm_moves_edge hred j
    have hget : fs.get i =
        cond (L.get j).2 (generatorPerm hred (L.get j).1)
          (generatorPerm hred (L.get j).1)⁻¹ := by
      simp only [fs, List.get_eq_getElem, List.getElem_map, j]
      simp only [Fin.val_cast]
    have hsource : x i.succ = edgeStart L j := by
      apply Fin.rev_injective
      apply Fin.ext
      rfl
    have hend : x i.castSucc = edgeEnd L j := by
      apply Fin.rev_injective
      apply Fin.ext
      rfl
    rw [hget, hsource, hend]
    exact hmove
  have hprod := perm_prod_moves_path fs x hstep
  rw [separatingHom, FreeGroup.lift_mk]
  change fs.prod 0 = Fin.last L.length
  have hlast : x (Fin.last fs.length) = 0 := by
    apply Fin.ext
    simp [x, fs]
  have hzero : x 0 = Fin.last L.length := by
    apply Fin.ext
    simp [x, fs]
  rwa [hlast, hzero] at hprod

private theorem separatingHom_mk_ne_one
    {L : List (α × Bool)} (hred : FreeGroup.IsReduced L) (hne : L ≠ []) :
    separatingHom hred (FreeGroup.mk L) ≠ 1 := by
  intro heq
  have happ := congrArg
    (fun σ : Equiv.Perm (Fin (L.length + 1)) ↦ σ 0) heq
  rw [separatingHom_mk_moves_endpoints hred] at happ
  simp only [Equiv.Perm.one_apply] at happ
  have hpos : 0 < L.length := List.length_pos_iff_ne_nil.mpr hne
  have hval := congrArg Fin.val happ
  simp only [Fin.val_last, Fin.val_zero] at hval
  omega

/-- Every free group is residually finite.  A nontrivial element is separated
from the identity by a permutation representation on one more point than the
length of its reduced word. -/
instance freeGroupResiduallyFinite (α : Type u) :
    Group.ResiduallyFinite (FreeGroup α) := by
  classical
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  let L := g.toWord
  have hne : L ≠ [] := by
    intro hnil
    apply hg
    exact FreeGroup.toWord_eq_nil_iff.mp (by simpa only [L] using hnil)
  have hred : FreeGroup.IsReduced L := by
    simpa only [L] using (FreeGroup.isReduced_toWord (x := g))
  refine ⟨Equiv.Perm (Fin (L.length + 1)), inferInstance, inferInstance,
    separatingHom hred, ?_⟩
  rw [← FreeGroup.mk_toWord (x := g)]
  exact separatingHom_mk_ne_one hred hne

/-- Any group carrying a free-group structure is torsion-free. -/
theorem isMulTorsionFreeOfIsFreeGroup
    (G : Type u) [Group G] [IsFreeGroup G] : IsMulTorsionFree G where
  pow_left_injective n hn x y hxy := by
    let e := IsFreeGroup.toFreeGroup G
    apply e.injective
    apply IsMulTorsionFree.pow_left_injective hn
    simpa only [map_pow] using congrArg e hxy

/-- Any group carrying a free-group structure is residually finite. -/
theorem residuallyFiniteOfIsFreeGroup
    (G : Type u) [Group G] [IsFreeGroup G] :
    Group.ResiduallyFinite G := by
  let e := IsFreeGroup.toFreeGroup G
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  have heg : e g ≠ 1 := by
    intro h
    apply hg
    exact e.injective (by simpa using h)
  obtain ⟨H, hH⟩ :=
    Group.exists_finiteIndexNormalSubgroup_notMem (e g) heg
  let f : G →* FreeGroup (IsFreeGroup.Generators G) ⧸ H.toSubgroup :=
    (QuotientGroup.mk' H.toSubgroup).comp e.toMonoidHom
  exact ⟨FreeGroup (IsFreeGroup.Generators G) ⧸ H.toSubgroup,
    inferInstance, inferInstance, f, by
      change QuotientGroup.mk' H.toSubgroup (e g) ≠ 1
      intro h
      exact hH ((QuotientGroup.eq_one_iff (e g)).mp h)⟩

end MagnitudeConjecture
