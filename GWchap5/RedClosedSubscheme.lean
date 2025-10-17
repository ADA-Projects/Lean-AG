import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Ideal.Operations

import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Irreducible

open CategoryTheory TopologicalSpace AlgebraicGeometry RingedSpace Ideal Topology Prime

variable {X : Scheme} {T : Set X.carrier}

/-- The reduced closed subscheme with underlying set T -/
noncomputable
def reducedClosedSubscheme (T : Closeds X) : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal T).subscheme

/-- The closed immersion from the reduced closed subscheme to X -/
noncomputable
def reducedClosedSubscheme_ι (T : Closeds X) :
    reducedClosedSubscheme T ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal T).subschemeι

/-- The underlying set of the reduced closed subscheme equals T. -/
lemma reducedClosedSubscheme_support (T : Closeds X) :
    Set.range (reducedClosedSubscheme_ι T).base = (T : Set X) := by
  simp [reducedClosedSubscheme, reducedClosedSubscheme_ι]

/-- The reduced closed subscheme is reduced -/
lemma reducedClosedSubscheme_isReduced (T : Closeds X) :
    IsReduced (reducedClosedSubscheme T) := by
  have h_stalks_reduced : ∀ x, IsReduced ((reducedClosedSubscheme T).presheaf.stalk x) := by
    intro x
    let I := Scheme.IdealSheafData.vanishingIdeal T
    let 𝒰 := I.subschemeCover
    let i := 𝒰.idx x
    obtain ⟨x', hx'⟩ := 𝒰.covers x
    rw [← hx']
    let f := 𝒰.f i
    haveI : IsIso (f.stalkMap x') := by infer_instance
    suffices IsReduced ((Spec (𝒰.X i)).presheaf.stalk x') by
      apply isReduced_of_injective (f.stalkMap x').hom
      exact (isIso_iff_bijective _).mp inferInstance |>.left
    haveI : IsReduced (Spec (𝒰.X i)) := by
      rw [affine_isReduced_iff]
      change IsReduced (Γ(X, i.1) ⧸ I.ideal i)
      rw [← Ideal.isRadical_iff_quotient_reduced]
      --exact Ideal.radical_isRadical i.1
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    exact isReduced_stalk_of_isReduced (Spec (𝒰.X i)) x'
  exact isReduced_of_isReduced_stalk _

-- Helper lemmas for the uniqueness proof
/-- The constructed reduced closed subscheme satisfies the required properties. -/
lemma reducedClosedSubscheme_properties (T : Closeds X) :
    IsClosedImmersion (reducedClosedSubscheme_ι T) ∧
    Set.range (reducedClosedSubscheme_ι T).base = (T : Set X) ∧
    IsReduced (reducedClosedSubscheme T) := by
  refine ⟨?_, reducedClosedSubscheme_support T, reducedClosedSubscheme_isReduced T⟩
  · unfold reducedClosedSubscheme_ι
    apply IsClosedImmersion.of_isPreimmersion
    change IsClosed (Set.range (reducedClosedSubscheme_ι T).base)
    rw [reducedClosedSubscheme_support]
    exact T.isClosed

/-- The support of the kernel of a closed immersion equals the closure of its range. -/
lemma ker_support_eq_closure_range {Z : Scheme} (f : Z ⟶ X)
    [IsClosedImmersion f] :
    f.ker.support = closure (Set.range f.base) :=
  Scheme.Hom.support_ker f

/-- The kernel of a closed immersion with reduced domain is a radical ideal sheaf. -/
lemma ker_of_reduced_isRadical {Z : Scheme} (f : Z ⟶ X) [IsClosedImmersion f]
    (hf_reduced : IsReduced Z) : f.ker.radical = f.ker := by
  ext U : 2
  rw [f.ker.radical_ideal, f.ker_apply, radical_eq_iff, Ideal.isRadical_iff_quotient_reduced]
  let e := RingHom.quotientKerEquivRange (f.app U).hom
  have : IsReduced (RingHom.range (f.app U).hom) := by
    haveI : IsReduced (Γ(Z, f ⁻¹ᵁ U)) := hf_reduced.component_reduced (f ⁻¹ᵁ U)
    rw [isReduced_iff]
    intro y hy
    rw [← Subring.coe_eq_zero_iff, ← isNilpotent_iff_eq_zero]
    exact hy.map (Subring.subtype _)
  apply isReduced_of_injective e.toRingHom
  exact e.injective

/-- For a reduced closed immersion with range T, the kernel equals the vanishing ideal. -/
lemma ker_eq_vanishingIdeal (T : Closeds X) {Z : Scheme} (f : Z ⟶ X)
    [IsClosedImmersion f] (hf_range : Set.range f.base = (T : Set X))
    (hf_reduced : IsReduced Z) :
    f.ker = Scheme.IdealSheafData.vanishingIdeal T := by
  have h_ker_is_rad : f.ker.radical = f.ker := ker_of_reduced_isRadical f hf_reduced
  rw [← h_ker_is_rad, ← @Scheme.IdealSheafData.vanishingIdeal_support]
  congr 1
  apply Closeds.ext
  rw [ker_support_eq_closure_range f, hf_range, T.isClosed.closure_eq]

/-- Two closed immersions into the same scheme with the same kernel are isomorphic. -/
@[simps hom inv]
noncomputable
def isoOfEqKer {Z₁ Z₂ : Scheme} {f₁ : Z₁ ⟶ X} {f₂ : Z₂ ⟶ X}
    [IsClosedImmersion f₁] [IsClosedImmersion f₂] (h_ker : f₁.ker = f₂.ker) : Z₁ ≅ Z₂ where
  hom := IsClosedImmersion.lift f₂ f₁ h_ker.ge
  inv := IsClosedImmersion.lift f₁ f₂ h_ker.le
  hom_inv_id := (cancel_mono f₁).mp (by simp [IsClosedImmersion.lift_fac])
  inv_hom_id := (cancel_mono f₂).mp (by simp [IsClosedImmersion.lift_fac])

/-- There exists a reduced closed subscheme with underlying set `T`,
and it is unique up to a unique isomorphism. -/
theorem unique_reduced_closed_subscheme (T : Closeds X) :
  ∃ (Z' : Over X), IsClosedImmersion Z'.hom ∧ Set.range Z'.hom.base = (T : Set X) ∧
    IsReduced Z'.left ∧ ∀ (Z₂ : Over X) [IsClosedImmersion Z₂.hom],
      Set.range Z₂.hom.base = (T : Set X) → IsReduced Z₂.left → Nonempty (Z' ≅ Z₂) := by
  use Over.mk (reducedClosedSubscheme_ι T)
  have prop := reducedClosedSubscheme_properties T
  refine ⟨prop.1, prop.2.1, prop.2.2, ?_⟩
  intro Z₂ h_range h_range h_red
  fapply Nonempty.intro
  haveI H_prop1 := prop.1
  have h_kernels_eq : Z₂.hom.ker = (reducedClosedSubscheme_ι T).ker := by
    rw [ker_eq_vanishingIdeal T Z₂.hom h_range h_red,
      ker_eq_vanishingIdeal T (reducedClosedSubscheme_ι T) prop.2.1 prop.2.2]
  let e : Z₂.left ≅ reducedClosedSubscheme T := isoOfEqKer h_kernels_eq
  fapply Over.isoMk e.symm
