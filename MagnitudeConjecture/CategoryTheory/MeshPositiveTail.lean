import MagnitudeConjecture.CategoryTheory.FiniteMeshEndLocal
import MagnitudeConjecture.CategoryTheory.MeshIncomingDecomposition
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# The positive tail of a mesh representable

For a vertex `z`, the morphisms into `z` of positive path length are exactly
the sums of morphisms followed by one arrow into `z`.  This is the first exact
part of the standard mesh presentation of the simple contravariant functor at
`z`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped BigOperators

namespace MagnitudeConjecture.MeshCategory

universe u v w

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]
variable [∀ x : Q, Fintype (Σ y : Q, x ⟶ y)]

namespace RightMeshData

variable (T : RightMeshData Q)

/-- A represented quiver arrow into a vertex has path degree one. -/
theorem incomingArrowHom_mem_lengthComponent_one {z : Q}
    (a : IncomingArrow z) :
    T.incomingArrowHom (k := k) a ∈
      lengthComponent (k := k) T a.1 z 1 := by
  refine ⟨MagnitudeConjecture.LinearPathCategory.pathHom a.2.toPath, ?_, rfl⟩
  exact (MagnitudeConjecture.LinearPathCategory.pathHom_mem_lengthComponent_iff
    (k := k) a.2.toPath 1).2 rfl

/-- A represented quiver arrow out of a vertex has path degree one. -/
theorem outgoingArrowHom_mem_lengthComponent_one {x : Q}
    (a : OutgoingArrow x) :
    T.outgoingArrowHom (k := k) a ∈
      lengthComponent (k := k) T x a.1 1 := by
  refine ⟨MagnitudeConjecture.LinearPathCategory.pathHom a.2.toPath, ?_, rfl⟩
  exact (MagnitudeConjecture.LinearPathCategory.pathHom_mem_lengthComponent_iff
    (k := k) a.2.toPath 1).2 rfl

/-- The incoming-arrow sum, regarded as a linear map from its coefficient
space to the target Hom space. -/
def incomingSumLinearMap (x z : Q) :
    IncomingCoefficient (k := k) T x z →ₗ[k]
      (obj (k := k) T x ⟶ obj (k := k) T z) where
  toFun := T.incomingSum
  map_add' := by
    intro c d
    simp [incomingSum, Preadditive.add_comp, Finset.sum_add_distrib]
  map_smul' := by
    intro r c
    simp [incomingSum, CategoryTheory.Linear.smul_comp, Finset.smul_sum]

@[simp]
theorem incomingSumLinearMap_apply {x z : Q}
    (c : IncomingCoefficient (k := k) T x z) :
    T.incomingSumLinearMap (k := k) x z c = T.incomingSum c :=
  rfl

/-- Every sum through the incoming arrows has positive path length. -/
theorem incomingSum_mem_lengthTail_one {x z : Q}
    (c : IncomingCoefficient (k := k) T x z) :
    T.incomingSum c ∈ lengthTail (k := k) T x z 1 := by
  rw [incomingSum]
  apply Submodule.sum_mem
  intro a _
  have hc : c a ∈ lengthTail (k := k) T x a.1 0 := by
    rw [lengthTail_zero_eq_top]
    exact Submodule.mem_top
  have ha : T.incomingArrowHom (k := k) a ∈
      lengthTail (k := k) T a.1 z 1 :=
    mem_lengthTail_of_mem_lengthComponent (k := k) T (by omega)
      (T.incomingArrowHom_mem_lengthComponent_one (k := k) a)
  simpa using comp_mem_lengthTail (k := k) T hc ha

/-- A scalar multiple of a vertex identity can have positive path length only
when its scalar is zero. -/
theorem smul_id_mem_lengthTail_one_iff (x : Q) (c : k) :
    c • 𝟙 (obj (k := k) T x) ∈ lengthTail (k := k) T x x 1 ↔ c = 0 := by
  constructor
  · intro hc
    by_contra hne
    have hid : 𝟙 (obj (k := k) T x) ∈ lengthTail (k := k) T x x 1 := by
      have hinv := Submodule.smul_mem
        (lengthTail (k := k) T x x 1) c⁻¹ hc
      simpa [hne] using hinv
    exact id_not_mem_lengthTail_one (k := k) T x hid
  · rintro rfl
    simp

/-- A diagonal scalar term lying in the positive tail vanishes.  For unequal
vertices it is zero by definition; at one vertex this is degree separation. -/
theorem diagonalScalar_eq_zero_of_mem_lengthTail_one {x z : Q} (c : k)
    (hc : T.diagonalScalar (k := k) x z c ∈
      lengthTail (k := k) T x z 1) :
    T.diagonalScalar (k := k) x z c = 0 := by
  by_cases hxz : x = z
  · subst z
    rw [T.diagonalScalar_self] at hc ⊢
    have hczero := (T.smul_id_mem_lengthTail_one_iff (k := k) x c).mp hc
    simp [hczero]
  · simp [diagonalScalar, hxz]

/-- The image of the incoming-arrow map is exactly the positive-length tail
of the contravariant representable at its target. -/
theorem range_incomingSumLinearMap_eq_lengthTail_one (x z : Q) :
    LinearMap.range (T.incomingSumLinearMap (k := k) x z) =
      lengthTail (k := k) T x z 1 := by
  apply le_antisymm
  · rintro f ⟨c, rfl⟩
    exact T.incomingSum_mem_lengthTail_one (k := k) c
  · intro f hf
    obtain ⟨c, h, hdecomp⟩ :=
      T.exists_eq_diagonalScalar_add_incomingSum f
    have hsum : T.incomingSum h ∈ lengthTail (k := k) T x z 1 :=
      T.incomingSum_mem_lengthTail_one (k := k) h
    have hdiag : T.diagonalScalar (k := k) x z c ∈
        lengthTail (k := k) T x z 1 := by
      have heq : T.diagonalScalar (k := k) x z c = f - T.incomingSum h := by
        rw [hdecomp]
        module
      rw [heq]
      exact Submodule.sub_mem _ hf hsum
    have hdiagzero :=
      T.diagonalScalar_eq_zero_of_mem_lengthTail_one (k := k) c hdiag
    refine ⟨h, ?_⟩
    rw [incomingSumLinearMap_apply, hdecomp, hdiagzero, zero_add]

/-- The value at `x` of the simple contravariant mesh functor supported at
`z`: the representable Hom space modulo all positive-length morphisms. -/
abbrev simpleValue (x z : Q) :=
  (obj (k := k) T x ⟶ obj (k := k) T z) ⧸
    lengthTail (k := k) T x z 1

/-- The canonical projection from the representable Hom space to the simple
value. -/
def simpleValueProjection (x z : Q) :
    (obj (k := k) T x ⟶ obj (k := k) T z) →ₗ[k]
      T.simpleValue (k := k) x z :=
  (lengthTail (k := k) T x z 1).mkQ

theorem simpleValueProjection_surjective (x z : Q) :
    Function.Surjective (T.simpleValueProjection (k := k) x z) :=
  (lengthTail (k := k) T x z 1).mkQ_surjective

/-- Objectwise exactness at the representable: the kernel of projection to
the simple value is exactly the image of all incoming arrows. -/
theorem ker_simpleValueProjection_eq_range_incomingSumLinearMap (x z : Q) :
    LinearMap.ker (T.simpleValueProjection (k := k) x z) =
      LinearMap.range (T.incomingSumLinearMap (k := k) x z) := by
  rw [simpleValueProjection, (lengthTail (k := k) T x z 1).ker_mkQ,
    T.range_incomingSumLinearMap_eq_lengthTail_one (k := k) x z]

/-- Away from its supporting vertex, the simple mesh value is zero. -/
theorem simpleValue_subsingleton_of_ne {x z : Q} (hxz : x ≠ z) :
    Subsingleton (T.simpleValue (k := k) x z) := by
  change Subsingleton
    ((obj (k := k) T x ⟶ obj (k := k) T z) ⧸
      lengthTail (k := k) T x z 1)
  rw [lengthTail_one_eq_top_of_ne (k := k) T hxz.symm]
  infer_instance

/-- Scalar multiples of the identity map into the value of the simple mesh
functor at its supporting vertex. -/
def simpleValueSelfScalarLinearMap (z : Q) :
    k →ₗ[k] T.simpleValue (k := k) z z :=
  (T.simpleValueProjection (k := k) z z).comp
    ((LinearMap.lsmul k
      (obj (k := k) T z ⟶ obj (k := k) T z)).flip
        (𝟙 (obj (k := k) T z)))

@[simp]
theorem simpleValueSelfScalarLinearMap_apply (z : Q) (c : k) :
    T.simpleValueSelfScalarLinearMap (k := k) z c =
      T.simpleValueProjection (k := k) z z
        (c • 𝟙 (obj (k := k) T z)) :=
  rfl

/-- At its supporting vertex, the simple mesh value is one-dimensional, with
the identity class as its canonical basis vector. -/
theorem simpleValueSelfScalarLinearMap_bijective (z : Q) :
    Function.Bijective (T.simpleValueSelfScalarLinearMap (k := k) z) := by
  constructor
  · intro c d hcd
    apply sub_eq_zero.mp
    apply (T.smul_id_mem_lengthTail_one_iff (k := k) z (c - d)).mp
    rw [← (lengthTail (k := k) T z z 1).ker_mkQ, LinearMap.mem_ker]
    have hsub := congrArg
      (fun q : T.simpleValue (k := k) z z ↦
        q - T.simpleValueSelfScalarLinearMap (k := k) z d) hcd
    simpa [simpleValueSelfScalarLinearMap_apply, simpleValueProjection,
      sub_smul] using hsub
  · intro q
    obtain ⟨f, rfl⟩ := T.simpleValueProjection_surjective (k := k) z z q
    obtain ⟨c, h, hdecomp⟩ :=
      T.exists_eq_diagonalScalar_add_incomingSum f
    refine ⟨c, ?_⟩
    have hsum : T.incomingSum h ∈ lengthTail (k := k) T z z 1 :=
      T.incomingSum_mem_lengthTail_one (k := k) h
    have hsumzero :
        T.simpleValueProjection (k := k) z z (T.incomingSum h) = 0 := by
      rw [simpleValueProjection, ← LinearMap.mem_ker,
        (lengthTail (k := k) T z z 1).ker_mkQ]
      exact hsum
    have hq := congrArg (T.simpleValueProjection (k := k) z z) hdecomp
    rw [T.diagonalScalar_self, map_add, hsumzero, add_zero] at hq
    simpa only [simpleValueSelfScalarLinearMap_apply] using hq.symm

/-- The canonical identification of the supporting value of a mesh simple
with the coefficient field. -/
noncomputable def simpleValueSelfLinearEquiv (z : Q) :
    k ≃ₗ[k] T.simpleValue (k := k) z z :=
  LinearEquiv.ofBijective (T.simpleValueSelfScalarLinearMap (k := k) z)
    (T.simpleValueSelfScalarLinearMap_bijective (k := k) z)

/-- Precomposition preserves the positive tail in the contravariant
representable. -/
theorem precomp_mem_lengthTail_one {x y z : Q}
    (f : obj (k := k) T y ⟶ obj (k := k) T x)
    {q : obj (k := k) T x ⟶ obj (k := k) T z}
    (hq : q ∈ lengthTail (k := k) T x z 1) :
    f ≫ q ∈ lengthTail (k := k) T y z 1 := by
  have hf : f ∈ lengthTail (k := k) T y x 0 := by
    rw [lengthTail_zero_eq_top]
    exact Submodule.mem_top
  simpa using comp_mem_lengthTail (k := k) T hf hq

/-- The strict vertex model of the raw mesh category.  Its objects are the
quiver vertices themselves and its Hom spaces are the corresponding raw mesh
Hom spaces. -/
abbrev VertexCategory :=
  InducedCategory (RawCategory (k := k) T) (obj (k := k) T)

/-- The simple contravariant mesh functor supported at `z`. -/
def simpleFunctor (z : Q) :
    (T.VertexCategory (k := k))ᵒᵖ ⥤ ModuleCat k where
  obj X := ModuleCat.of k (T.simpleValue (k := k) X.unop z)
  map {X Y} f := ModuleCat.ofHom <|
    Submodule.mapQ
      (lengthTail (k := k) T X.unop z 1)
      (lengthTail (k := k) T Y.unop z 1)
      (CategoryTheory.Linear.leftComp k (obj (k := k) T z) f.unop.hom)
      (by
        intro q hq
        exact T.precomp_mem_lengthTail_one (k := k) f.unop.hom hq)
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro q
    induction q using Submodule.Quotient.induction_on with
    | _ q =>
      change Submodule.Quotient.mk
          ((𝟙 X.unop : X.unop ⟶ X.unop).hom ≫ q) =
        Submodule.Quotient.mk q
      rw [InducedCategory.id_hom, Category.id_comp]
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro q
    induction q using Submodule.Quotient.induction_on with
    | _ q =>
      change Submodule.Quotient.mk ((g.unop ≫ f.unop).hom ≫ q) =
        Submodule.Quotient.mk
          (g.unop.hom ≫ f.unop.hom ≫ q)
      rw [InducedCategory.comp_hom, Category.assoc]

/-- The representable presheaf projects naturally onto the mesh simple. -/
def simpleProjection (z : Q) :
    (CategoryTheory.linearYoneda k (T.VertexCategory (k := k))).obj z ⟶
      T.simpleFunctor (k := k) z where
  app X := ModuleCat.ofHom
    ((T.simpleValueProjection (k := k) X.unop z).comp
      InducedCategory.homLinearEquiv.toLinearMap)
  naturality := by
    intro X Y f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    rfl

instance simpleProjection_epi (z : Q) :
    Epi (T.simpleProjection (k := k) z) := by
  haveI happ (X : (T.VertexCategory (k := k))ᵒᵖ) :
      Epi ((T.simpleProjection (k := k) z).app X) := by
    rw [ModuleCat.epi_iff_surjective]
    exact (T.simpleValueProjection_surjective (k := k) X.unop z).comp
      InducedCategory.homLinearEquiv.surjective
  exact NatTrans.epi_of_epi_app _

/-- The finite family of contravariant representables indexed by the arrows
into `z`, presented objectwise as its coefficient product. -/
def incomingCoefficientFunctor (z : Q) :
    (T.VertexCategory (k := k))ᵒᵖ ⥤ ModuleCat k where
  obj X := ModuleCat.of k
    (IncomingCoefficient (k := k) T X.unop z)
  map {X Y} f := ModuleCat.ofHom
    { toFun := fun c a ↦ f.unop.hom ≫ c a
      map_add' := by
        intro c d
        funext a
        change f.unop.hom ≫ (c a + d a) =
          f.unop.hom ≫ c a + f.unop.hom ≫ d a
        rw [Preadditive.comp_add]
      map_smul' := by
        intro r c
        funext a
        change f.unop.hom ≫ (r • c a) = r • (f.unop.hom ≫ c a)
        rw [CategoryTheory.Linear.comp_smul] }
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    change (𝟙 X.unop : X.unop ⟶ X.unop).hom ≫ c a = c a
    rw [InducedCategory.id_hom, Category.id_comp]
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    change (g.unop ≫ f.unop).hom ≫ c a =
      g.unop.hom ≫ f.unop.hom ≫ c a
    rw [InducedCategory.comp_hom, Category.assoc]

/-- Summing after the incoming arrows is a natural map from the incoming
coefficient functor to the representable at `z`. -/
def incomingMap (z : Q) :
    T.incomingCoefficientFunctor (k := k) z ⟶
      (CategoryTheory.linearYoneda k (T.VertexCategory (k := k))).obj z where
  app X := ModuleCat.ofHom
    (InducedCategory.homLinearEquiv.symm.toLinearMap.comp
      (T.incomingSumLinearMap (k := k) X.unop z))
  naturality := by
    intro X Y f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply InducedCategory.hom_ext
    change T.incomingSum
        (fun a : IncomingArrow z ↦ f.unop.hom ≫ c a) =
      f.unop.hom ≫ T.incomingSum c
    rw [incomingSum, incomingSum]
    classical
    let s : Finset (IncomingArrow z) := Finset.univ
    change (∑ a ∈ s, (f.unop.hom ≫ c a) ≫ T.incomingArrowHom a) =
      f.unop.hom ≫ (∑ a ∈ s, c a ≫ T.incomingArrowHom a)
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        Preadditive.comp_add, Category.assoc, ih]

/-- The incoming-arrow map followed by projection to the mesh simple is zero. -/
theorem incomingMap_comp_simpleProjection (z : Q) :
    T.incomingMap (k := k) z ≫ T.simpleProjection (k := k) z = 0 := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change T.simpleValueProjection (k := k) X.unop z
      (T.incomingSum c) = 0
  rw [← LinearMap.mem_ker,
    T.ker_simpleValueProjection_eq_range_incomingSumLinearMap (k := k)]
  exact ⟨c, rfl⟩

/-- Exactness of the incoming-arrow presentation at every object of the raw
mesh category. -/
theorem range_incomingMap_app_eq_ker_simpleProjection_app (z : Q)
    (X : (T.VertexCategory (k := k))ᵒᵖ) :
    LinearMap.range ((T.incomingMap (k := k) z).app X).hom =
      LinearMap.ker ((T.simpleProjection (k := k) z).app X).hom := by
  let e : (X.unop ⟶ (z : T.VertexCategory (k := k))) ≃ₗ[k]
      (obj (k := k) T X.unop ⟶ obj (k := k) T z) :=
    InducedCategory.homLinearEquiv
  change LinearMap.range
      (e.symm.toLinearMap.comp
        (T.incomingSumLinearMap (k := k) X.unop z)) =
    LinearMap.ker
      ((T.simpleValueProjection (k := k) X.unop z).comp e.toLinearMap)
  ext q
  constructor
  · rintro ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    change T.simpleValueProjection (k := k) X.unop z
      (e (e.symm (T.incomingSum c))) = 0
    rw [e.apply_symm_apply, ← LinearMap.mem_ker,
      T.ker_simpleValueProjection_eq_range_incomingSumLinearMap (k := k)]
    exact ⟨c, rfl⟩
  · intro hq
    rw [LinearMap.mem_ker] at hq
    have hrange : e q ∈
        LinearMap.range (T.incomingSumLinearMap (k := k) X.unop z) := by
      rw [← T.ker_simpleValueProjection_eq_range_incomingSumLinearMap
        (k := k), LinearMap.mem_ker]
      exact hq
    obtain ⟨c, hc⟩ := hrange
    refine ⟨c, ?_⟩
    apply e.injective
    change e (e.symm (T.incomingSum c)) = e q
    rw [e.apply_symm_apply]
    exact hc

end RightMeshData

end MagnitudeConjecture.MeshCategory
