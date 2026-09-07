import MagnitudeConjecture.Algebra.UniserialModule

/-!
# Socles of finite-length modules

This file supplies the intrinsic dual of the simple-top interface used in the
Pogorzały--Skowroński induction.  The socle is the sum of all simple
submodules.  In an Artinian module it meets every nonzero submodule, so a
simple socle forces indecomposability.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture

universe u v

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The socle of a module, realized as the sum of all its simple
submodules. -/
def moduleSocle (R : Type u) (M : Type v)
    [Ring R] [AddCommGroup M] [Module R M] : Submodule R M :=
  sSup {S : Submodule R M | IsSimpleModule R S}

/-- The socle, being the sum of the simple submodules, is semisimple. -/
theorem moduleSocle_isSemisimple :
    IsSemisimpleModule R (moduleSocle R M) := by
  unfold moduleSocle
  rw [sSup_eq_iSup]
  exact isSemisimpleModule_biSup_of_isSemisimpleModule_submodule
    (fun S hS ↦ by
      letI : IsSimpleModule R S := hS
      infer_instance)

/-- Every simple submodule is contained in the socle. -/
theorem le_moduleSocle_of_simple
    (S : Submodule R M) (hS : IsSimpleModule R S) :
    S ≤ moduleSocle R M :=
  le_sSup hS

/-- The image of a simple submodule under an injective linear map is
simple. -/
theorem isSimpleModule_map_of_injective
    {N : Type v} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f)
    (S : Submodule R M) (hS : IsSimpleModule R S) :
    IsSimpleModule R (S.map f) := by
  let g := f.domRestrict S
  let e : S ≃ₗ[R] LinearMap.range g :=
    LinearEquiv.ofInjective g (hf.comp S.subtype_injective)
  have hrange : LinearMap.range g = S.map f := by
    ext y
    simp [g]
  rw [← hrange]
  letI : IsSimpleModule R S := hS
  exact IsSimpleModule.congr e.symm

/-- The image of a simple submodule under an arbitrary linear map is either
zero or simple. -/
theorem map_eq_bot_or_isSimpleModule
    {N : Type v} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (S : Submodule R M)
    (hS : IsSimpleModule R S) :
    S.map f = ⊥ ∨ IsSimpleModule R (S.map f) := by
  let g : S →ₗ[R] N := f.domRestrict S
  have hrange : LinearMap.range g = S.map f := by
    ext y
    simp [g]
  letI : IsSimpleModule R S := hS
  rcases IsSimpleOrder.eq_bot_or_eq_top (LinearMap.ker g) with hker | hker
  · right
    rw [← hrange]
    let e : S ≃ₗ[R] LinearMap.range g :=
      LinearEquiv.ofInjective g (LinearMap.ker_eq_bot.mp hker)
    exact IsSimpleModule.congr e.symm
  · left
    rw [← hrange, LinearMap.range_eq_bot]
    apply LinearMap.ext
    intro x
    exact LinearMap.mem_ker.mp (hker ▸ Submodule.mem_top)

/-- Every linear map sends the source socle into the target socle. -/
theorem map_moduleSocle_le
    {N : Type v} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    (moduleSocle R M).map f ≤ moduleSocle R N := by
  rw [Submodule.map_le_iff_le_comap]
  unfold moduleSocle
  apply sSup_le
  intro S hSsimple
  rw [← Submodule.map_le_iff_le_comap]
  rcases map_eq_bot_or_isSimpleModule f S hSsimple with hzero | hsimple
  · rw [hzero]
    exact bot_le
  · exact le_moduleSocle_of_simple (S.map f) hsimple

/-- An injective linear map sends the source socle into the target
socle. -/
theorem map_moduleSocle_le_of_injective
    {N : Type v} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (_hf : Function.Injective f) :
    (moduleSocle R M).map f ≤ moduleSocle R N := by
  exact map_moduleSocle_le f

/-- Pulling the ambient socle back to a submodule gives the intrinsic socle
of that submodule. -/
theorem comap_moduleSocle_subtype_eq_moduleSocle
    (P : Submodule R M) :
    (moduleSocle R M).comap P.subtype = moduleSocle R P := by
  apply le_antisymm
  · let T : Submodule R P := (moduleSocle R M).comap P.subtype
    let f : T →ₗ[R] moduleSocle R M := {
      toFun := fun x ↦ ⟨x.1.1, x.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : moduleSocle R M ↦ (z : M)) hxy
    letI : IsSemisimpleModule R (moduleSocle R M) :=
      moduleSocle_isSemisimple
    letI : IsSemisimpleModule R T :=
      IsSemisimpleModule.of_injective f hf
    have hmap : (moduleSocle R T).map T.subtype ≤ moduleSocle R P :=
      map_moduleSocle_le_of_injective T.subtype T.subtype_injective
    rw [show moduleSocle R T = ⊤ from
        IsSemisimpleModule.sSup_simples_eq_top R T,
      Submodule.map_top, Submodule.range_subtype] at hmap
    exact hmap
  · rw [← Submodule.map_le_iff_le_comap]
    exact map_moduleSocle_le_of_injective P.subtype P.subtype_injective

/-- A linear equivalence carries the socle onto the socle. -/
theorem map_moduleSocle_eq_of_linearEquiv
    {N : Type v} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    (moduleSocle R M).map e.toLinearMap = moduleSocle R N := by
  apply le_antisymm
  · exact map_moduleSocle_le_of_injective e.toLinearMap e.injective
  · intro y hy
    have hback :
        (moduleSocle R N).map e.symm.toLinearMap ≤ moduleSocle R M :=
      map_moduleSocle_le_of_injective e.symm.toLinearMap e.symm.injective
    have hpre : e.symm y ∈ moduleSocle R M :=
      hback ⟨y, hy, rfl⟩
    exact ⟨e.symm y, hpre, e.apply_symm_apply y⟩

/-- Having simple socle is invariant under a linear equivalence. -/
theorem simple_moduleSocle_congr
    {N : Type v} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (hM : IsSimpleModule R (moduleSocle R M)) :
    IsSimpleModule R (moduleSocle R N) := by
  have hmap :
      IsSimpleModule R ((moduleSocle R M).map e.toLinearMap) := by
    letI : IsSimpleModule R (moduleSocle R M) := hM
    exact IsSimpleModule.congr (e.submoduleMap (moduleSocle R M)).symm
  rw [map_moduleSocle_eq_of_linearEquiv e] at hmap
  exact hmap

/-- The socle of a binary product is the product of the two socles. -/
theorem moduleSocle_prod
    {N : Type v} [AddCommGroup N] [Module R N] :
    moduleSocle R (M × N) =
      (moduleSocle R M).prod (moduleSocle R N) := by
  apply le_antisymm
  · unfold moduleSocle
    apply sSup_le
    intro S hSsimple x hx
    constructor
    · let p : (M × N) →ₗ[R] M := LinearMap.fst R M N
      have hxp : x.1 ∈ S.map p := ⟨x, hx, rfl⟩
      rcases map_eq_bot_or_isSimpleModule p S hSsimple with hzero | hsimple
      · have hxzero : x.1 = 0 := by
          simpa [hzero] using hxp
        simp [hxzero]
      · exact le_moduleSocle_of_simple (S.map p) hsimple hxp
    · let q : (M × N) →ₗ[R] N := LinearMap.snd R M N
      have hxq : x.2 ∈ S.map q := ⟨x, hx, rfl⟩
      rcases map_eq_bot_or_isSimpleModule q S hSsimple with hzero | hsimple
      · have hxzero : x.2 = 0 := by
          simpa [hzero] using hxq
        simp [hxzero]
      · exact le_moduleSocle_of_simple (S.map q) hsimple hxq
  · intro x hx
    have hinl :
        (moduleSocle R M).map (LinearMap.inl R M N) ≤
          moduleSocle R (M × N) :=
      map_moduleSocle_le_of_injective
        (LinearMap.inl R M N) LinearMap.inl_injective
    have hinr :
        (moduleSocle R N).map (LinearMap.inr R M N) ≤
          moduleSocle R (M × N) :=
      map_moduleSocle_le_of_injective
        (LinearMap.inr R M N) LinearMap.inr_injective
    have hleft : (x.1, 0) ∈ moduleSocle R (M × N) :=
      hinl ⟨x.1, hx.1, rfl⟩
    have hright : (0, x.2) ∈ moduleSocle R (M × N) :=
      hinr ⟨x.2, hx.2, rfl⟩
    simpa using (moduleSocle R (M × N)).add_mem hleft hright

/-- A simple submodule of the product of two non-isomorphic simple modules is
one of the two coordinate submodules. -/
theorem simpleSubmodule_prod_eq_coordinate
    {N : Type v} [AddCommGroup N] [Module R N]
    (hM : IsSimpleModule R M) (hN : IsSimpleModule R N)
    (hnoniso : ¬ Nonempty (M ≃ₗ[R] N))
    (P : Submodule R (M × N)) (hP : IsSimpleModule R P) :
    P = LinearMap.range (LinearMap.inl R M N) ∨
      P = LinearMap.range (LinearMap.inr R M N) := by
  let pM : P →ₗ[R] M := (LinearMap.fst R M N).comp P.subtype
  let pN : P →ₗ[R] N := (LinearMap.snd R M N).comp P.subtype
  letI : IsSimpleModule R P := hP
  letI : IsSimpleModule R M := hM
  letI : IsSimpleModule R N := hN
  have hzero : pM = 0 ∨ pN = 0 := by
    by_contra h
    simp only [not_or] at h
    apply hnoniso
    let eM : P ≃ₗ[R] M := LinearEquiv.ofBijective pM
      (LinearMap.bijective_of_ne_zero h.1)
    let eN : P ≃ₗ[R] N := LinearEquiv.ofBijective pN
      (LinearMap.bijective_of_ne_zero h.2)
    exact ⟨eM.symm.trans eN⟩
  have hPne : P ≠ ⊥ := (isSimpleModule_iff_isAtom.mp hP).ne_bot
  rcases hzero with hpM | hpN
  · right
    have hcoordSimple : IsSimpleModule R
        (LinearMap.range (LinearMap.inr R M N)) :=
      IsSimpleModule.congr
        (LinearEquiv.ofInjective (LinearMap.inr R M N)
          LinearMap.inr_injective).symm
    have hle : P ≤ LinearMap.range (LinearMap.inr R M N) := by
      intro x hx
      have hxzero : x.1 = 0 := by
        have := LinearMap.congr_fun hpM ⟨x, hx⟩
        simpa [pM] using this
      exact ⟨x.2, by ext <;> simp [hxzero]⟩
    exact (isSimpleModule_iff_isAtom.mp hcoordSimple).le_iff_eq hPne |>.mp hle
  · left
    have hcoordSimple : IsSimpleModule R
        (LinearMap.range (LinearMap.inl R M N)) :=
      IsSimpleModule.congr
        (LinearEquiv.ofInjective (LinearMap.inl R M N)
          LinearMap.inl_injective).symm
    have hle : P ≤ LinearMap.range (LinearMap.inl R M N) := by
      intro x hx
      have hxzero : x.2 = 0 := by
        have := LinearMap.congr_fun hpN ⟨x, hx⟩
        simpa [pN] using this
      exact ⟨x.1, by ext <;> simp [hxzero]⟩
    exact (isSimpleModule_iff_isAtom.mp hcoordSimple).le_iff_eq hPne |>.mp hle

/-- The product of two submodule types is linearly equivalent to the subtype
of their product submodule. -/
def submoduleProdLinearEquiv
    {N : Type v} [AddCommGroup N] [Module R N]
    (P : Submodule R M) (Q : Submodule R N) :
    (P × Q) ≃ₗ[R] (P.prod Q) where
  toFun x := ⟨(x.1.1, x.2.1), x.1.2, x.2.2⟩
  invFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A complementary decomposition restricts to a linear equivalence from
the product of the two summand socles onto the ambient socle. -/
def moduleSocleProdLinearEquivOfIsCompl
    (P Q : Submodule R M) (hPQ : IsCompl P Q) :
    (moduleSocle R P × moduleSocle R Q) ≃ₗ[R] moduleSocle R M :=
  (submoduleProdLinearEquiv
      (moduleSocle R P) (moduleSocle R Q)).trans
    ((LinearEquiv.ofEq
      ((moduleSocle R P).prod (moduleSocle R Q))
      (moduleSocle R (P × Q))
      (moduleSocle_prod (R := R) (M := P) (N := Q)).symm).trans
    (((P.prodEquivOfIsCompl Q hPQ).submoduleMap
      (moduleSocle R (P × Q))).trans
    (LinearEquiv.ofEq _ _
      (map_moduleSocle_eq_of_linearEquiv
        (P.prodEquivOfIsCompl Q hPQ)))))

/-- Quotienting a complementary decomposition by the socles of its two
summands gives the quotient of the ambient module by its socle. -/
def quotientModuleSocleProdLinearEquivOfIsCompl
    (P Q : Submodule R M) (hPQ : IsCompl P Q) :
    ((P ⧸ moduleSocle R P) × (Q ⧸ moduleSocle R Q)) ≃ₗ[R]
      (M ⧸ moduleSocle R M) :=
  let q : (P × Q) →ₗ[R]
      ((P ⧸ moduleSocle R P) × (Q ⧸ moduleSocle R Q)) :=
    (moduleSocle R P).mkQ.prodMap (moduleSocle R Q).mkQ
  let hq : Function.Surjective q := by
    intro x
    obtain ⟨p, hp⟩ := (moduleSocle R P).mkQ_surjective x.1
    obtain ⟨q', hq'⟩ := (moduleSocle R Q).mkQ_surjective x.2
    exact ⟨(p, q'), Prod.ext hp hq'⟩
  let eProd :
      ((P ⧸ moduleSocle R P) × (Q ⧸ moduleSocle R Q)) ≃ₗ[R]
        ((P × Q) ⧸
          (moduleSocle R P).prod (moduleSocle R Q)) :=
    (q.quotKerEquivOfSurjective hq).symm.trans
      (Submodule.quotEquivOfEq q.ker
        ((moduleSocle R P).prod (moduleSocle R Q)) (by
          simp [q]))
  let ePQ : (P × Q) ≃ₗ[R] M := P.prodEquivOfIsCompl Q hPQ
  let hsocle :
      ((moduleSocle R P).prod (moduleSocle R Q)).map ePQ.toLinearMap =
        moduleSocle R M := by
    rw [← moduleSocle_prod]
    exact map_moduleSocle_eq_of_linearEquiv ePQ
  eProd.trans (Submodule.Quotient.equiv
    ((moduleSocle R P).prod (moduleSocle R Q))
    (moduleSocle R M) ePQ hsocle)

/-- A complementary decomposition restricts, after quotienting by the first
socle layer, to a linear equivalence from the product of the two next socle
layers onto the ambient next socle layer. -/
def quotientModuleSocleLayerProdLinearEquivOfIsCompl
    (P Q : Submodule R M) (hPQ : IsCompl P Q) :
    (moduleSocle R (P ⧸ moduleSocle R P) ×
      moduleSocle R (Q ⧸ moduleSocle R Q)) ≃ₗ[R]
        moduleSocle R (M ⧸ moduleSocle R M) :=
  let e := quotientModuleSocleProdLinearEquivOfIsCompl P Q hPQ
  (submoduleProdLinearEquiv
      (moduleSocle R (P ⧸ moduleSocle R P))
      (moduleSocle R (Q ⧸ moduleSocle R Q))).trans
    ((LinearEquiv.ofEq
      ((moduleSocle R (P ⧸ moduleSocle R P)).prod
        (moduleSocle R (Q ⧸ moduleSocle R Q)))
      (moduleSocle R
        ((P ⧸ moduleSocle R P) × (Q ⧸ moduleSocle R Q)))
      (moduleSocle_prod (R := R)).symm).trans
    ((e.submoduleMap
      (moduleSocle R
        ((P ⧸ moduleSocle R P) × (Q ⧸ moduleSocle R Q)))).trans
    (LinearEquiv.ofEq _ _ (map_moduleSocle_eq_of_linearEquiv e))))

/-- The next socle-layer length is additive across a complementary
decomposition. -/
theorem length_quotientModuleSocleLayer_eq_add_of_isCompl
    (P Q : Submodule R M) (hPQ : IsCompl P Q) :
    Module.length R (moduleSocle R (M ⧸ moduleSocle R M)) =
      Module.length R (moduleSocle R (P ⧸ moduleSocle R P)) +
        Module.length R (moduleSocle R (Q ⧸ moduleSocle R Q)) := by
  calc
    Module.length R (moduleSocle R (M ⧸ moduleSocle R M)) =
        Module.length R
          (moduleSocle R (P ⧸ moduleSocle R P) ×
            moduleSocle R (Q ⧸ moduleSocle R Q)) :=
      (quotientModuleSocleLayerProdLinearEquivOfIsCompl P Q hPQ).length_eq.symm
    _ = Module.length R (moduleSocle R (P ⧸ moduleSocle R P)) +
        Module.length R (moduleSocle R (Q ⧸ moduleSocle R Q)) :=
      Module.length_prod R _ _

/-- Composition length of the socle is additive across a complementary
decomposition. -/
theorem length_moduleSocle_eq_add_of_isCompl
    (P Q : Submodule R M) (hPQ : IsCompl P Q) :
    Module.length R (moduleSocle R M) =
      Module.length R (moduleSocle R P) +
        Module.length R (moduleSocle R Q) := by
  calc
    Module.length R (moduleSocle R M) =
        Module.length R
          (moduleSocle R P × moduleSocle R Q) :=
      (moduleSocleProdLinearEquivOfIsCompl P Q hPQ).length_eq.symm
    _ = Module.length R (moduleSocle R P) +
        Module.length R (moduleSocle R Q) := Module.length_prod R _ _

/-- Every nonzero submodule of an Artinian module contains a simple
submodule. -/
theorem exists_simple_submodule_le
    [IsArtinian R M] (P : Submodule R M) (hP : P ≠ ⊥) :
    ∃ S : Submodule R M, IsSimpleModule R S ∧ S ≤ P := by
  obtain ⟨S, hSatom, hSP⟩ :=
    (eq_bot_or_exists_atom_le P).resolve_left hP
  exact ⟨S, isSimpleModule_iff_isAtom.mpr hSatom, hSP⟩

/-- In an Artinian module the socle meets every nonzero submodule
nontrivially. -/
theorem inf_moduleSocle_ne_bot
    [IsArtinian R M] (P : Submodule R M) (hP : P ≠ ⊥) :
    P ⊓ moduleSocle R M ≠ ⊥ := by
  obtain ⟨S, hSsimple, hSP⟩ := exists_simple_submodule_le P hP
  have hSsocle : S ≤ moduleSocle R M :=
    le_moduleSocle_of_simple S hSsimple
  have hSinf : S ≤ P ⊓ moduleSocle R M := le_inf hSP hSsocle
  have hSne : S ≠ ⊥ :=
    (isSimpleModule_iff_isAtom.mp hSsimple).ne_bot
  intro hinf
  apply hSne
  exact le_antisymm (hinf ▸ hSinf) bot_le

/-- If an Artinian module has simple socle, every noninjective linear map
out of it kills that socle. -/
theorem moduleSocle_le_ker_of_not_injective
    [IsArtinian R M]
    {N : Type v} [AddCommGroup N] [Module R N]
    (hsocle : IsSimpleModule R (moduleSocle R M))
    (f : M →ₗ[R] N) (hf : ¬ Function.Injective f) :
    moduleSocle R M ≤ LinearMap.ker f := by
  have hkerNe : LinearMap.ker f ≠ ⊥ := by
    intro hker
    exact hf (LinearMap.ker_eq_bot.mp hker)
  have hinfNe : LinearMap.ker f ⊓ moduleSocle R M ≠ ⊥ :=
    inf_moduleSocle_ne_bot (LinearMap.ker f) hkerNe
  have hinfEq : LinearMap.ker f ⊓ moduleSocle R M = moduleSocle R M :=
    (isSimpleModule_iff_isAtom.mp hsocle).le_iff_eq hinfNe |>.mp inf_le_right
  rw [← hinfEq]
  exact inf_le_left

/-- The socle of a nonzero Artinian module is nonzero. -/
theorem moduleSocle_ne_bot
    [IsArtinian R M] [Nontrivial M] :
    moduleSocle R M ≠ ⊥ := by
  intro hsocle
  apply inf_moduleSocle_ne_bot
    (R := R) (M := M) (⊤ : Submodule R M) top_ne_bot
  simp [hsocle]

/-- An injective map from a nonzero Artinian module into a module with
simple socle forces the source socle to be simple. -/
theorem moduleSocle_isSimple_of_injective
    {N : Type v} [AddCommGroup N] [Module R N]
    [IsArtinian R M] [Nontrivial M]
    (f : M →ₗ[R] N) (hf : Function.Injective f)
    (hN : IsSimpleModule R (moduleSocle R N)) :
    IsSimpleModule R (moduleSocle R M) := by
  let SM := moduleSocle R M
  let SN := moduleSocle R N
  have hmapLe : SM.map f ≤ SN :=
    map_moduleSocle_le_of_injective f hf
  have hSMne : SM ≠ ⊥ := moduleSocle_ne_bot
  have hmapNe : SM.map f ≠ ⊥ := by
    intro hzero
    apply hSMne
    apply le_antisymm
    · intro x hx
      have hfx : f x = 0 := by
        have : f x ∈ SM.map f := ⟨x, hx, rfl⟩
        simpa [hzero] using this
      exact hf (hfx.trans (map_zero f).symm)
    · exact bot_le
  have hmapEq : SM.map f = SN :=
    (isSimpleModule_iff_isAtom.mp hN).le_iff_eq hmapNe |>.mp hmapLe
  let g : SM →ₗ[R] N := f.domRestrict SM
  let eRange : SM ≃ₗ[R] LinearMap.range g :=
    LinearEquiv.ofInjective g (hf.comp SM.subtype_injective)
  have hrange : LinearMap.range g = SM.map f := by
    ext y
    simp [g]
  let e : SM ≃ₗ[R] SN :=
    eRange.trans (LinearEquiv.ofEq _ _ (hrange.trans hmapEq))
  letI : IsSimpleModule R SN := hN
  exact IsSimpleModule.congr e

/-- If a noetherian module has simple top but is not itself simple, its
socle lies in its Jacobson radical. -/
theorem moduleSocle_le_jacobson_of_simpleTop_of_not_simple
    [IsNoetherian R M]
    (htop : IsSimpleModule R (M ⧸ Module.jacobson R M))
    (hnotSimple : ¬ IsSimpleModule R M) :
    moduleSocle R M ≤ Module.jacobson R M := by
  unfold moduleSocle
  apply sSup_le
  intro S hSsimple
  apply IsUniserialModule.le_jacobson_of_ne_top_of_simple_top htop
  intro hStop
  apply hnotSimple
  letI : IsSimpleModule R S := hSsimple
  exact IsSimpleModule.congr (LinearEquiv.ofTop S hStop).symm

/-- A nonzero Artinian uniserial module has simple socle. -/
theorem IsUniserialModule.moduleSocle_isSimple
    [IsArtinian R M] [Nontrivial M]
    (hM : IsUniserialModule R M) :
    IsSimpleModule R (moduleSocle R M) := by
  obtain ⟨S, hSatom, -⟩ :=
    (eq_bot_or_exists_atom_le
      (⊤ : Submodule R M)).resolve_left top_ne_bot
  have hSsimple : IsSimpleModule R S :=
    isSimpleModule_iff_isAtom.mpr hSatom
  have hSle : S ≤ moduleSocle R M :=
    le_moduleSocle_of_simple S hSsimple
  have hsocleLe : moduleSocle R M ≤ S := by
    apply sSup_le
    intro T hTsimple
    have hTatom : IsAtom T :=
      isSimpleModule_iff_isAtom.mp hTsimple
    unfold IsUniserialModule at hM
    rcases hM.total T S with hTS | hST
    · exact hTS
    · have hTS : T = S :=
        ((hTatom.le_iff_eq hSatom.ne_bot).mp hST).symm
      exact hTS.le
  rw [le_antisymm hsocleLe hSle]
  exact hSsimple

/-- In a uniserial module, every specified simple submodule is the socle. -/
theorem IsUniserialModule.moduleSocle_eq_of_simple_submodule
    (hM : IsUniserialModule R M)
    (P : Submodule R M) (hP : IsSimpleModule R P) :
    moduleSocle R M = P := by
  apply le_antisymm
  · unfold moduleSocle
    apply sSup_le
    intro Q hQ
    rcases hM.total Q P with hQP | hPQ
    · exact hQP
    · have hQatom : IsAtom Q := isSimpleModule_iff_isAtom.mp hQ
      exact ((hQatom.le_iff_eq
        (isSimpleModule_iff_isAtom.mp hP).ne_bot).mp hPQ).ge
  · exact le_moduleSocle_of_simple P hP

/-- Two simple ambient submodules contained in the same uniserial submodule
are equal. -/
theorem IsUniserialModule.eq_of_simple_submodules_le
    {U P Q : Submodule R M}
    (hU : IsUniserialModule R U)
    (hP : IsSimpleModule R P) (hQ : IsSimpleModule R Q)
    (hPU : P ≤ U) (hQU : Q ≤ U) :
    P = Q := by
  let PU : Submodule R U := P.comap U.subtype
  let QU : Submodule R U := Q.comap U.subtype
  let eP : PU ≃ₗ[R] P := Submodule.comapSubtypeEquivOfLe hPU
  let eQ : QU ≃ₗ[R] Q := Submodule.comapSubtypeEquivOfLe hQU
  letI : IsSimpleModule R P := hP
  letI : IsSimpleModule R Q := hQ
  have hPUsimple : IsSimpleModule R PU := IsSimpleModule.congr eP
  have hQUsimple : IsSimpleModule R QU := IsSimpleModule.congr eQ
  have hPUne : PU ≠ ⊥ :=
    Submodule.nontrivial_iff_ne_bot.mp hPUsimple.nontrivial
  have hQUne : QU ≠ ⊥ :=
    Submodule.nontrivial_iff_ne_bot.mp hQUsimple.nontrivial
  have hPQU : PU = QU := by
    rcases hU.total PU QU with hle | hle
    · exact ((isSimpleModule_iff_isAtom.mp hQUsimple).le_iff_eq hPUne).mp hle
    · exact
        (((isSimpleModule_iff_isAtom.mp hPUsimple).le_iff_eq hQUne).mp hle).symm
  calc
    P = PU.map U.subtype := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hPU]
    _ = QU.map U.subtype := by rw [hPQU]
    _ = Q := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hQU]

/-- An Artinian module is uniserial when its socle is simple and the
quotient by that socle is uniserial.  The simple socle is essential, so
every nonzero submodule is recovered from its image in the quotient. -/
theorem IsUniserialModule.of_simpleSocle_of_quotient_moduleSocle
    [IsArtinian R M]
    (hsocle : IsSimpleModule R (moduleSocle R M))
    (hquot : IsUniserialModule R (M ⧸ moduleSocle R M)) :
    IsUniserialModule R M := by
  let S : Submodule R M := moduleSocle R M
  have hSatom : IsAtom S := isSimpleModule_iff_isAtom.mp hsocle
  have socle_le_of_ne_bot (P : Submodule R M) (hP : P ≠ ⊥) : S ≤ P := by
    have hinf : P ⊓ S ≠ ⊥ := inf_moduleSocle_ne_bot P hP
    have heq : P ⊓ S = S :=
      (hSatom.le_iff_eq hinf).mp inf_le_right
    rw [← heq]
    exact inf_le_left
  unfold IsUniserialModule at hquot ⊢
  constructor
  intro P Q
  by_cases hP : P = ⊥
  · exact Or.inl (hP ▸ bot_le)
  by_cases hQ : Q = ⊥
  · exact Or.inr (hQ ▸ bot_le)
  have hSP : S ≤ P := socle_le_of_ne_bot P hP
  have hSQ : S ≤ Q := socle_le_of_ne_bot Q hQ
  rcases hquot.total (P.map S.mkQ) (Q.map S.mkQ) with hPQ | hQP
  · left
    rw [← Submodule.comap_map_eq_self (f := S.mkQ) (p := P)
        (by simpa using hSP),
      ← Submodule.comap_map_eq_self (f := S.mkQ) (p := Q)
        (by simpa using hSQ)]
    exact Submodule.comap_mono hPQ
  · right
    rw [← Submodule.comap_map_eq_self (f := S.mkQ) (p := Q)
        (by simpa using hSQ),
      ← Submodule.comap_map_eq_self (f := S.mkQ) (p := P)
        (by simpa using hSP)]
    exact Submodule.comap_mono hQP

/-- If quotienting by a specified simple submodule makes an Artinian module
uniserial, then failure of uniseriality is witnessed by a second simple
submodule disjoint from the specified one. -/
theorem exists_disjoint_simple_submodule_of_simple_quotient_uniserial
    [IsArtinian R M]
    (I : Submodule R M) (hI : IsSimpleModule R I)
    (hquot : IsUniserialModule R (M ⧸ I))
    (hnotuni : ¬ IsUniserialModule R M) :
    ∃ S : Submodule R M,
      IsSimpleModule R S ∧ S ⊓ I = ⊥ := by
  have hsocleNotSimple :
      ¬ IsSimpleModule R (moduleSocle R M) := by
    intro hsocle
    have hIle : I ≤ moduleSocle R M :=
      le_moduleSocle_of_simple I hI
    have hIne : I ≠ ⊥ :=
      (isSimpleModule_iff_isAtom.mp hI).ne_bot
    have hsocleEq : moduleSocle R M = I := by
      exact
        (((isSimpleModule_iff_isAtom.mp hsocle).le_iff_eq hIne).mp hIle).symm
    apply hnotuni
    apply IsUniserialModule.of_simpleSocle_of_quotient_moduleSocle hsocle
    rw [hsocleEq]
    exact hquot
  have hexists : ∃ S : Submodule R M,
      IsSimpleModule R S ∧ ¬ S ≤ I := by
    by_contra hnone
    have hall : ∀ S : Submodule R M,
        IsSimpleModule R S → S ≤ I := by
      intro S hS
      by_contra hSnotle
      exact hnone ⟨S, hS, hSnotle⟩
    have hsocleLe : moduleSocle R M ≤ I := by
      unfold moduleSocle
      exact sSup_le hall
    have hIle : I ≤ moduleSocle R M :=
      le_moduleSocle_of_simple I hI
    apply hsocleNotSimple
    rw [le_antisymm hsocleLe hIle]
    exact hI
  obtain ⟨S, hS, hSnotle⟩ := hexists
  refine ⟨S, hS, ?_⟩
  by_contra hinf
  have hinfEq : S ⊓ I = S :=
    ((isSimpleModule_iff_isAtom.mp hS).le_iff_eq hinf).mp inf_le_left
  apply hSnotle
  rw [← hinfEq]
  exact inf_le_right

/-- A length-two module with simple socle is uniserial. -/
theorem uniserial_of_simpleSocle_of_length_eq_two
    [IsArtinian R M]
    (hsocle : IsSimpleModule R (moduleSocle R M))
    (hlength : Module.length R M = 2) :
    IsUniserialModule R M := by
  let S : Submodule R M := moduleSocle R M
  have hSlength : Module.length R S = 1 :=
    Module.length_eq_one_iff.mpr hsocle
  have hexact : Module.length R M =
      Module.length R S + Module.length R (M ⧸ S) :=
    Module.length_eq_add_of_exact
      S.subtype S.mkQ S.subtype_injective S.mkQ_surjective
      (LinearMap.exact_subtype_mkQ S)
  have hquotLength : Module.length R (M ⧸ S) = 1 := by
    rw [hlength, hSlength] at hexact
    apply WithTop.add_left_cancel ENat.one_ne_top
    calc
      1 + Module.length R (M ⧸ S) = 2 := hexact.symm
      _ = 1 + 1 := by norm_num
  apply IsUniserialModule.of_simpleSocle_of_quotient_moduleSocle hsocle
  have hsimple : IsSimpleModule R (M ⧸ S) :=
    Module.length_eq_one_iff.mp hquotLength
  letI : IsSimpleModule R (M ⧸ S) := hsimple
  unfold IsUniserialModule
  constructor
  intro P Q
  rcases IsSimpleOrder.eq_bot_or_eq_top P with rfl | rfl
  · exact Or.inl bot_le
  · exact Or.inr le_top

/-- Removing a simple socle from a length-three module leaves a module of
length two. -/
theorem length_quotient_moduleSocle_eq_two_of_length_eq_three
    (hsocle : IsSimpleModule R (moduleSocle R M))
    (hlength : Module.length R M = 3) :
    Module.length R (M ⧸ moduleSocle R M) = 2 := by
  let S : Submodule R M := moduleSocle R M
  have hSlength : Module.length R S = 1 :=
    Module.length_eq_one_iff.mpr hsocle
  have hexact : Module.length R M =
      Module.length R S + Module.length R (M ⧸ S) :=
    Module.length_eq_add_of_exact
      S.subtype S.mkQ S.subtype_injective S.mkQ_surjective
      (LinearMap.exact_subtype_mkQ S)
  rw [hlength, hSlength] at hexact
  apply WithTop.add_left_cancel ENat.one_ne_top
  calc
    1 + Module.length R (M ⧸ S) = 3 := hexact.symm
    _ = 1 + 2 := by norm_num

/-- Quotienting a length-four module by a simple submodule leaves length
three. -/
theorem length_quotient_eq_three_of_length_eq_four_of_simple
    (P : Submodule R M)
    (hMlength : Module.length R M = 4)
    (hPsimple : IsSimpleModule R P) :
    Module.length R (M ⧸ P) = 3 := by
  have hPlength : Module.length R P = 1 :=
    Module.length_eq_one_iff.mpr hPsimple
  have hexact : Module.length R M =
      Module.length R P + Module.length R (M ⧸ P) :=
    Module.length_eq_add_of_exact
      P.subtype P.mkQ P.subtype_injective P.mkQ_surjective
      (LinearMap.exact_subtype_mkQ P)
  rw [hMlength, hPlength] at hexact
  apply WithTop.add_left_cancel ENat.one_ne_top
  calc
    1 + Module.length R (M ⧸ P) = 4 := hexact.symm
    _ = 1 + 3 := by norm_num

/-- A surjection from a length-two module onto a length-one module kills the
simple socle of its source. -/
theorem moduleSocle_le_ker_of_surjective_of_length_eq_two_to_one
    {N : Type v} [AddCommGroup N] [Module R N]
    [IsArtinian R M]
    (q : M →ₗ[R] N) (hq : Function.Surjective q)
    (hMlength : Module.length R M = 2)
    (hNlength : Module.length R N = 1)
    (hsocle : IsSimpleModule R (moduleSocle R M)) :
    moduleSocle R M ≤ q.ker := by
  have hexact : Module.length R M =
      Module.length R q.ker + Module.length R N :=
    Module.length_eq_add_of_exact
      q.ker.subtype q q.ker.subtype_injective hq
      (LinearMap.exact_subtype_ker_map q)
  have hkerLength : Module.length R q.ker = 1 := by
    rw [hMlength, hNlength] at hexact
    apply WithTop.add_right_cancel ENat.one_ne_top
    calc
      Module.length R q.ker + 1 = 2 := hexact.symm
      _ = 1 + 1 := by norm_num
  have hkerNe : q.ker ≠ ⊥ := by
    intro hker
    have hzero : Module.length R q.ker = 0 := by
      rw [hker]
      exact Module.length_eq_zero
    rw [hkerLength] at hzero
    norm_num at hzero
  have hinf : q.ker ⊓ moduleSocle R M ≠ ⊥ :=
    inf_moduleSocle_ne_bot q.ker hkerNe
  have hsocleAtom : IsAtom (moduleSocle R M) :=
    isSimpleModule_iff_isAtom.mp hsocle
  have hinfEq : q.ker ⊓ moduleSocle R M = moduleSocle R M :=
    (hsocleAtom.le_iff_eq hinf).mp inf_le_right
  rw [← hinfEq]
  exact inf_le_left

/-- A length-three module is uniserial when its socle and the socle of its
quotient by the socle are both simple. -/
theorem uniserial_of_two_simple_socle_layers_of_length_eq_three
    [IsArtinian R M]
    (hsocle : IsSimpleModule R (moduleSocle R M))
    (hnext : IsSimpleModule R
      (moduleSocle R (M ⧸ moduleSocle R M)))
    (hlength : Module.length R M = 3) :
    IsUniserialModule R M := by
  let S : Submodule R M := moduleSocle R M
  have hquotLength : Module.length R (M ⧸ S) = 2 :=
    length_quotient_moduleSocle_eq_two_of_length_eq_three hsocle hlength
  apply IsUniserialModule.of_simpleSocle_of_quotient_moduleSocle hsocle
  exact uniserial_of_simpleSocle_of_length_eq_two hnext hquotLength

/-- An Artinian module with simple socle is indecomposable.  This is the
simple-socle dual of the existing simple-top criterion. -/
theorem isIndecomposableModule_of_simpleSocle
    [IsArtinian R M]
    (hsocle : IsSimpleModule R (moduleSocle R M)) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R M := by
  have hsocleAtom : IsAtom (moduleSocle R M) :=
    isSimpleModule_iff_isAtom.mp hsocle
  letI : Nontrivial M := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hM
    exact hsocleAtom.ne_bot (Subsingleton.elim _ _)
  apply
    QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isCompl
  intro P Q hPQ
  by_cases hP : P = ⊥
  · exact Or.inl hP
  by_cases hQ : Q = ⊥
  · exact Or.inr hQ
  exfalso
  have hPinf : P ⊓ moduleSocle R M ≠ ⊥ :=
    inf_moduleSocle_ne_bot P hP
  have hQinf : Q ⊓ moduleSocle R M ≠ ⊥ :=
    inf_moduleSocle_ne_bot Q hQ
  have hPinfEq : P ⊓ moduleSocle R M = moduleSocle R M :=
    (hsocleAtom.le_iff_eq hPinf).mp inf_le_right
  have hQinfEq : Q ⊓ moduleSocle R M = moduleSocle R M :=
    (hsocleAtom.le_iff_eq hQinf).mp inf_le_right
  have hsocleP : moduleSocle R M ≤ P := by
    rw [← hPinfEq]
    exact inf_le_left
  have hsocleQ : moduleSocle R M ≤ Q := by
    rw [← hQinfEq]
    exact inf_le_left
  have hsocleBot : moduleSocle R M ≤ ⊥ := by
    rw [← hPQ.inf_eq_bot]
    exact le_inf hsocleP hsocleQ
  exact hsocleAtom.ne_bot (bot_unique hsocleBot)

end MagnitudeConjecture
