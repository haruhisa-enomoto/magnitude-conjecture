import MagnitudeConjecture.Algebra.StringDetectorSplitTransport

/-!
# Pair detectors as contextual complete-word detectors

For a nontrivial valid pair of oppositely polarized endpoint words, the
matching trivial outer boundaries identify the raw pair detector at the join
with the contextual detector of the complete pair word.  Change of split then
identifies it naturally with the canonical detector of that complete word.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open MagnitudeConjecture.LinearAlgebra.FiniteFiltration

namespace MagnitudeConjecture.BoundQuiver.StringWord.EndpointWord

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : SpecialBiserialPresentation k A Q}
variable {S : P.ArrowPolarization} {u₀ : Q} {t : Bool}

/-- At the join of a nontrivial complete pair word, the contextual right
lower space is exactly the raw lower space of the right half. -/
theorem splitRightLower_pairPosition
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse))
    (hlength : 0 < (pairWord L R hstring).length) :
    splitRightLower N S (pairWord L R hstring)
        (.ofPosition _ (pairPosition L R hstring)) =
      lowerSubspace N R := by
  change signedPathSubspace N R.path
      (lowerBoundarySubspace N
        (detectorEndpoint S (pairWord L R hstring)).sourceVertex) = _
  rw [lowerSubspace_eq_sourceVertexBoundaryTransport]
  have hsign := detectorEndpoint_pairWord_sourceSign_of_length_pos
    L R hstring hlength
  unfold sourceVertex
  rw [hsign]
  change signedPathSubspace N R.path
      (lowerBoundarySubspace N (EndpointWord.vertex P S R.source _)) = _
  rfl

/-- The analogous right upper-space identification. -/
theorem splitRightUpper_pairPosition
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse))
    (hlength : 0 < (pairWord L R hstring).length) :
    splitRightUpper N S (pairWord L R hstring)
        (.ofPosition _ (pairPosition L R hstring)) =
      upperSubspace N R := by
  change signedPathSubspace N R.path
      (upperBoundarySubspace N
        (detectorEndpoint S (pairWord L R hstring)).sourceVertex) = _
  rw [upperSubspace_eq_sourceVertexBoundaryTransport]
  have hsign := detectorEndpoint_pairWord_sourceSign_of_length_pos
    L R hstring hlength
  unfold sourceVertex
  rw [hsign]
  change signedPathSubspace N R.path
      (upperBoundarySubspace N (EndpointWord.vertex P S R.source _)) = _
  rfl

/-- At the same join, the contextual left lower space is exactly the raw
lower space of the left half. -/
theorem splitLeftLower_pairPosition
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse))
    (hlength : 0 < (pairWord L R hstring).length) :
    splitLeftLower N S (pairWord L R hstring)
        (.ofPosition _ (pairPosition L R hstring)) =
      lowerSubspace N L := by
  change signedPathSubspace N
      (pairPosition L R hstring).2.suffix.reverse
        (lowerBoundarySubspace N
          (detectorEndpoint S (pairWord L R hstring)).oppositeVertex) = _
  have hsuffix :
      (pairPosition L R hstring).2.suffix = L.path.reverse :=
    pairPosition_suffix L R hstring
  have hpath :
      (pairPosition L R hstring).2.suffix.reverse = L.path := by
    calc
      _ = L.path.reverse.reverse := congrArg Quiver.Path.reverse hsuffix
      _ = L.path := by simp
  rw [hpath, lowerSubspace_eq_sourceVertexBoundaryTransport]
  have hsign :=
    detectorEndpoint_pairWord_oppositeVertex_sourceSign_of_length_pos
      L R hstring hlength
  have hsign' : signedPathTargetSignOr S false
      (pairWord L R hstring).path = L.sourceSign := by
    simpa only [oppositeVertex, EndpointWord.vertex_sourceSign,
      Bool.not_not] using hsign
  have htarget := congrArg Bool.not hsign'
  unfold oppositeVertex sourceVertex
  rw [htarget]
  rfl

/-- The analogous left upper-space identification. -/
theorem splitLeftUpper_pairPosition
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse))
    (hlength : 0 < (pairWord L R hstring).length) :
    splitLeftUpper N S (pairWord L R hstring)
        (.ofPosition _ (pairPosition L R hstring)) =
      upperSubspace N L := by
  change signedPathSubspace N
      (pairPosition L R hstring).2.suffix.reverse
        (upperBoundarySubspace N
          (detectorEndpoint S (pairWord L R hstring)).oppositeVertex) = _
  have hsuffix :
      (pairPosition L R hstring).2.suffix = L.path.reverse :=
    pairPosition_suffix L R hstring
  have hpath :
      (pairPosition L R hstring).2.suffix.reverse = L.path := by
    calc
      _ = L.path.reverse.reverse := congrArg Quiver.Path.reverse hsuffix
      _ = L.path := by simp
  rw [hpath, upperSubspace_eq_sourceVertexBoundaryTransport]
  have hsign :=
    detectorEndpoint_pairWord_oppositeVertex_sourceSign_of_length_pos
      L R hstring hlength
  have hsign' : signedPathTargetSignOr S false
      (pairWord L R hstring).path = L.sourceSign := by
    simpa only [oppositeVertex, EndpointWord.vertex_sourceSign,
      Bool.not_not] using hsign
  have htarget := congrArg Bool.not hsign'
  unfold oppositeVertex sourceVertex
  rw [htarget]
  rfl

/-- The raw pair numerator is the contextual numerator at the displayed
join. -/
theorem pairDetectorNumerator_eq_splitDetectorNumerator_pairPosition
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse))
    (hlength : 0 < (pairWord L R hstring).length) :
    pairDetectorNumerator N L R =
      splitDetectorNumerator N S (pairWord L R hstring)
        (.ofPosition _ (pairPosition L R hstring)) := by
  unfold pairDetectorNumerator splitDetectorNumerator
  rw [splitLeftUpper_pairPosition N L R hstring hlength,
    splitRightUpper_pairPosition N L R hstring hlength]
  rfl

/-- The raw pair denominator is likewise the contextual denominator at the
join. -/
theorem pairDetectorDenominator_eq_splitDetectorDenominator_pairPosition
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse))
    (hlength : 0 < (pairWord L R hstring).length) :
    pairDetectorDenominator N L R =
      splitDetectorDenominator N S (pairWord L R hstring)
        (.ofPosition _ (pairPosition L R hstring)) := by
  unfold pairDetectorDenominator splitDetectorDenominator
  rw [splitLeftUpper_pairPosition N L R hstring hlength,
    splitRightLower_pairPosition N L R hstring hlength,
    splitLeftLower_pairPosition N L R hstring hlength,
    splitRightUpper_pairPosition N L R hstring hlength]
  rfl

/-- Canonical identification of a nontrivial raw pair detector with the
contextual detector at its join. -/
def pairDetectorSplitEquiv
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse))
    (hlength : 0 < (pairWord L R hstring).length) :
    PairDetectorSpace N L R ≃ₗ[k]
      SplitDetectorSpace N S (pairWord L R hstring)
        (.ofPosition _ (pairPosition L R hstring)) :=
  MagnitudeConjecture.LinearAlgebra.PairSubquotient.quotientEquivOfEq
    (pairDetectorNumerator N L R)
    (splitDetectorNumerator N S (pairWord L R hstring)
      (.ofPosition _ (pairPosition L R hstring)))
    (pairDetectorDenominator N L R)
    (splitDetectorDenominator N S (pairWord L R hstring)
      (.ofPosition _ (pairPosition L R hstring)))
    (pairDetectorNumerator_eq_splitDetectorNumerator_pairPosition
      N L R hstring hlength)
    (pairDetectorDenominator_eq_splitDetectorDenominator_pairPosition
      N L R hstring hlength)

@[simp]
theorem pairDetectorSplitEquiv_mk
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse))
    (hlength : 0 < (pairWord L R hstring).length)
    (x : pairDetectorNumerator N L R) :
    pairDetectorSplitEquiv N L R hstring hlength
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨x.1, by
          rw [← pairDetectorNumerator_eq_splitDetectorNumerator_pairPosition
            N L R hstring hlength]
          exact x.2⟩ : splitDetectorNumerator N S
            (pairWord L R hstring)
              (.ofPosition _ (pairPosition L R hstring))) := by
  exact MagnitudeConjecture.LinearAlgebra.PairSubquotient.quotientEquivOfEq_apply_mk
    _ _ _ _ _ _ x

/-- A nontrivial valid pair detector is naturally the canonical detector of
its complete pair word. -/
def pairDetectorCompleteWordEquiv
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse))
    (hlength : 0 < (pairWord L R hstring).length) :
    PairDetectorSpace N L R ≃ₗ[k]
      DetectorSpace N (detectorEndpoint S (pairWord L R hstring)) :=
  (pairDetectorSplitEquiv N L R hstring hlength).trans
    (splitDetectorSpacePositionEquiv N S (pairPosition L R hstring))

/-- The join identification commutes with every module morphism. -/
theorem pairDetectorSplitEquiv_naturality
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse))
    (hlength : 0 < (pairWord L R hstring).length)
    (q : PairDetectorSpace M L R) :
    pairDetectorSplitEquiv N L R hstring hlength
        (pairDetectorLinearMap f L R q) =
      splitDetectorLinearMap f S (pairWord L R hstring)
        (.ofPosition _ (pairPosition L R hstring))
        (pairDetectorSplitEquiv M L R hstring hlength q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      rw [pairDetectorLinearMap_mk, pairDetectorSplitEquiv_mk,
        pairDetectorSplitEquiv_mk, splitDetectorLinearMap_mk]
      rfl

/-- The complete-word equivalence is natural in the represented module. -/
theorem pairDetectorCompleteWordEquiv_naturality
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse))
    (hlength : 0 < (pairWord L R hstring).length)
    (q : PairDetectorSpace M L R) :
    pairDetectorCompleteWordEquiv N L R hstring hlength
        (pairDetectorLinearMap f L R q) =
      detectorLinearMap f (detectorEndpoint S (pairWord L R hstring))
        (pairDetectorCompleteWordEquiv M L R hstring hlength q) := by
  rw [pairDetectorCompleteWordEquiv, pairDetectorCompleteWordEquiv,
    LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    pairDetectorSplitEquiv_naturality]
  exact splitDetectorLinearMap_position f S (pairPosition L R hstring) _

/-- If a valid pair has total length zero, its left half is the opposite
polarized trivial word of its right half.  Thus its pair detector is already
the ordinary detector of the right endpoint word. -/
def pairDetectorRightEquiv_of_length_zero
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse))
    (hlength : (pairWord L R hstring).length = 0) :
    PairDetectorSpace N L R ≃ₗ[k]
      DetectorSpace N R := by
  have hsum : R.path.length + L.path.length = 0 := by
    change (R.path.comp L.path.reverse).length = 0 at hlength
    simpa only [Quiver.Path.length_comp, length_reverse] using hlength
  have hLzero : L.path.length = 0 := by omega
  have hLeq : L = R.oppositeVertex :=
    L.eq_vertex_of_word_length_eq_zero (by exact hLzero)
  subst L
  exact pairDetectorSpaceOppositeVertexEquiv N R

/-- The direct identification of a zero-length pair with its right detector
is natural in the represented module. -/
theorem pairDetectorRightEquiv_of_length_zero_naturality
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse))
    (hlength : (pairWord L R hstring).length = 0)
    (q : PairDetectorSpace M L R) :
    pairDetectorRightEquiv_of_length_zero N L R hstring hlength
        (pairDetectorLinearMap f L R q) =
      detectorLinearMap f R
        (pairDetectorRightEquiv_of_length_zero
          M L R hstring hlength q) := by
  have hsum : R.path.length + L.path.length = 0 := by
    change (R.path.comp L.path.reverse).length = 0 at hlength
    simpa only [Quiver.Path.length_comp, length_reverse] using hlength
  have hLzero : L.path.length = 0 := by omega
  have hLeq : L = R.oppositeVertex :=
    L.eq_vertex_of_word_length_eq_zero (by exact hLzero)
  subst L
  exact LinearMap.congr_fun (pairDetectorLinearMap_oppositeVertex f R) q

/-- A valid pair-detector map is bijective whenever every ordinary endpoint
detector map is bijective.  Nontrivial pairs use the complete pair word;
the sole length-zero case uses the right endpoint word directly. -/
theorem pairDetectorLinearMap_bijective_of_isString
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    (hdetector : ∀ {v : Q} {s : Bool} (C : EndpointWord S v s),
      Function.Bijective (detectorLinearMap f C))
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse)) :
    Function.Bijective (pairDetectorLinearMap f L R) := by
  by_cases hzero : (pairWord L R hstring).length = 0
  · let eM := pairDetectorRightEquiv_of_length_zero M L R hstring hzero
    let eN := pairDetectorRightEquiv_of_length_zero N L R hstring hzero
    have hdet := hdetector R
    constructor
    · intro q₁ q₂ hq
      apply eM.injective
      apply hdet.1
      rw [← pairDetectorRightEquiv_of_length_zero_naturality
          f L R hstring hzero q₁,
        ← pairDetectorRightEquiv_of_length_zero_naturality
          f L R hstring hzero q₂, hq]
    · intro y
      obtain ⟨z, hz⟩ := hdet.2 (eN y)
      obtain ⟨q, rfl⟩ := eM.surjective z
      refine ⟨q, ?_⟩
      apply eN.injective
      rw [pairDetectorRightEquiv_of_length_zero_naturality]
      exact hz
  · have hlength : 0 < (pairWord L R hstring).length := by omega
    let C := detectorEndpoint S (pairWord L R hstring)
    let eM := pairDetectorCompleteWordEquiv M L R hstring hlength
    let eN := pairDetectorCompleteWordEquiv N L R hstring hlength
    have hdet := hdetector C
    constructor
    · intro q₁ q₂ hq
      apply eM.injective
      apply hdet.1
      rw [← pairDetectorCompleteWordEquiv_naturality
          f L R hstring hlength q₁,
        ← pairDetectorCompleteWordEquiv_naturality
          f L R hstring hlength q₂, hq]
    · intro y
      obtain ⟨z, hz⟩ := hdet.2 (eN y)
      obtain ⟨q, rfl⟩ := eM.surjective z
      refine ⟨q, ?_⟩
      apply eN.injective
      rw [pairDetectorCompleteWordEquiv_naturality]
      exact hz

/-- Every pair-detector map is bijective under endpoint-detector
bijectivity: valid joins reduce to an ordinary detector, while invalid joins
have zero source and target quotients. -/
theorem pairDetectorLinearMap_bijective
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    (hdetector : ∀ {v : Q} {s : Bool} (C : EndpointWord S v s),
      Function.Bijective (detectorLinearMap f C))
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    Function.Bijective (pairDetectorLinearMap f L R) := by
  by_cases hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse)
  · exact pairDetectorLinearMap_bijective_of_isString
      f hdetector L R hstring
  · letI : Subsingleton (PairDetectorSpace M L R) :=
      pairDetectorSpace_subsingleton_of_not_isString M L R hstring
    letI : Subsingleton (PairDetectorSpace N L R) :=
      pairDetectorSpace_subsingleton_of_not_isString N L R hstring
    constructor
    · intro x y _
      exact Subsingleton.elim x y
    · intro y
      exact ⟨0, Subsingleton.elim _ y⟩

/-- Every map on a lexicographic grid layer is bijective under ordinary
endpoint-detector bijectivity. -/
theorem pairGridLinearMap_bijective
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    (hdetector : ∀ {v : Q} {s : Bool} (C : EndpointWord S v s),
      Function.Bijective (detectorLinearMap f C))
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    Function.Bijective (pairGridLinearMap f L R) := by
  let eM := pairGridDetectorEquiv M L R
  let eN := pairGridDetectorEquiv N L R
  have hpair := pairDetectorLinearMap_bijective f hdetector L R
  constructor
  · intro q₁ q₂ hq
    apply eM.injective
    apply hpair.1
    rw [← pairGridDetectorEquiv_naturality f L R q₁,
      ← pairGridDetectorEquiv_naturality f L R q₂, hq]
  · intro y
    obtain ⟨z, hz⟩ := hpair.2 (eN y)
    obtain ⟨q, rfl⟩ := eM.surjective z
    refine ⟨q, ?_⟩
    apply eN.injective
    rw [pairGridDetectorEquiv_naturality]
    exact hz

/-- One successive quotient of the ordered grid filtration, before its
identification with the corresponding pair-grid quotient. -/
abbrev OrderedGridLayerSpace
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] (i : Fin (Nat.card (GridWordIndex S u₀ t))) :=
  ((orderedGridFiltration (P := P) (S := S) (t := t) N).subspace i.succ ⧸
    ((orderedGridFiltration (P := P) (S := S) (t := t) N).subspace
      i.castSucc).comap
        ((orderedGridFiltration (P := P) (S := S) (t := t) N).subspace
          i.succ).subtype)

/-- The `i`th ordered-filtration quotient is canonically its literal
pair-grid quotient. -/
noncomputable def orderedGridLayerEquiv
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] (i : Fin (Nat.card (GridWordIndex S u₀ t))) :
    OrderedGridLayerSpace (P := P) (S := S) (t := t) N i ≃ₗ[k]
      PairGridSpace N
        (orderedGridWord (P := P) (S := S) (t := t) i).1
        (orderedGridWord (P := P) (S := S) (t := t) i).2 :=
  MagnitudeConjecture.LinearAlgebra.PairSubquotient.quotientEquivOfEq
    ((orderedGridFiltration (P := P) (S := S) (t := t) N).subspace i.succ)
    (pairGridUpper N
      (orderedGridWord (P := P) (S := S) (t := t) i).1
      (orderedGridWord (P := P) (S := S) (t := t) i).2)
    ((orderedGridFiltration (P := P) (S := S) (t := t) N).subspace
      i.castSucc)
    (pairGridLower N
      (orderedGridWord (P := P) (S := S) (t := t) i).1
      (orderedGridWord (P := P) (S := S) (t := t) i).2)
    (cumulativeGridSubspace_succ N i)
    (cumulativeGridSubspace_castSucc N i)

@[simp]
theorem orderedGridLayerEquiv_mk
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] (i : Fin (Nat.card (GridWordIndex S u₀ t)))
    (x : (orderedGridFiltration
      (P := P) (S := S) (t := t) N).subspace i.succ) :
    orderedGridLayerEquiv N i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨x.1, by
          rw [← cumulativeGridSubspace_succ N i]
          exact x.2⟩ : pairGridUpper N
            (orderedGridWord (P := P) (S := S) (t := t) i).1
            (orderedGridWord (P := P) (S := S) (t := t) i).2) := by
  exact MagnitudeConjecture.LinearAlgebra.PairSubquotient.quotientEquivOfEq_apply_mk
    _ _ _ _ _ _ x

/-- The ordered-layer identification commutes with every module morphism. -/
theorem orderedGridLayerEquiv_naturality
    [Finite (DetectorIndex S)]
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    (i : Fin (Nat.card (GridWordIndex S u₀ t)))
    (q : OrderedGridLayerSpace (P := P) (S := S) (t := t) M i) :
    orderedGridLayerEquiv N i
        (Filtration.gradedMap
          (f.app (Opposite.op (obj P.toPresentation.relations u₀))).hom
          (orderedGridFiltration (P := P) (S := S) (t := t) M)
          (orderedGridFiltration (P := P) (S := S) (t := t) N)
          (orderedGridFiltration_compatible
            (P := P) (S := S) (t := t) f) i q) =
      pairGridLinearMap f
        (orderedGridWord (P := P) (S := S) (t := t) i).1
        (orderedGridWord (P := P) (S := S) (t := t) i).2
        (orderedGridLayerEquiv M i q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      rw [Filtration.gradedMap, layerMap_mk,
        orderedGridLayerEquiv_mk, orderedGridLayerEquiv_mk,
        pairGridLinearMap_mk]
      rfl

/-- Every successive map in the ordered grid filtration is bijective under
ordinary endpoint-detector bijectivity. -/
theorem orderedGridFiltration_gradedMap_bijective
    [Finite (DetectorIndex S)]
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    (hdetector : ∀ {v : Q} {s : Bool} (C : EndpointWord S v s),
      Function.Bijective (detectorLinearMap f C))
    (i : Fin (Nat.card (GridWordIndex S u₀ t))) :
    Function.Bijective
      (Filtration.gradedMap
        (f.app (Opposite.op (obj P.toPresentation.relations u₀))).hom
        (orderedGridFiltration (P := P) (S := S) (t := t) M)
        (orderedGridFiltration (P := P) (S := S) (t := t) N)
        (orderedGridFiltration_compatible
          (P := P) (S := S) (t := t) f) i) := by
  let eM := orderedGridLayerEquiv (P := P) (S := S) (t := t) M i
  let eN := orderedGridLayerEquiv (P := P) (S := S) (t := t) N i
  have hgrid := pairGridLinearMap_bijective f hdetector
    (orderedGridWord (P := P) (S := S) (t := t) i).1
    (orderedGridWord (P := P) (S := S) (t := t) i).2
  constructor
  · intro q₁ q₂ hq
    apply eM.injective
    apply hgrid.1
    rw [← orderedGridLayerEquiv_naturality f i q₁,
      ← orderedGridLayerEquiv_naturality f i q₂, hq]
  · intro y
    obtain ⟨z, hz⟩ := hgrid.2 (eN y)
    obtain ⟨q, rfl⟩ := eM.surjective z
    refine ⟨q, ?_⟩
    apply eN.injective
    rw [orderedGridLayerEquiv_naturality]
    exact hz

end MagnitudeConjecture.BoundQuiver.StringWord.EndpointWord
