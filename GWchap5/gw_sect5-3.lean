/-
Copyright (c) 2024 Alessandro D'Angelo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.RingTheory.Ideal.Height
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Closure
import Mathlib.Topology.Irreducible

/-!
# Krull dimension of topological subspaces

This file establishes fundamental properties of topological Krull dimension for subspaces,
proper closed subsets, open coverings, irreducible components, and schemes.

The topological Krull dimension of a topological space is defined as the Krull dimension of the
poset of irreducible closed subsets. This file proves several key relationships between
dimensions of spaces and their subspaces.

## Main results

- `topKrullDim_subspace_le`: For any subspace $Y \subseteq X$, we have $\dim(Y) \leq \dim(X)$
- `topological_dim_proper_closed_subset_lt`: For a proper closed subset $Y \subsetneq X$
  of an irreducible space with finite dimension, $\dim(Y) < \dim(X)$
- `topological_dim_open_cover`: For an open cover $X = \bigcup_i U_i$,
  $\dim(X) = \sup_i \dim(U_i)$
- `topological_dim_irreducible_components`:
  $\dim(X) = \sup_{Y \in \text{IrredComponents}(X)} \dim(Y)$
- `scheme_dim_eq_sup_local_rings`: For a scheme $X$,
  $\dim(X) = \sup_{x \in X} \dim(\mathcal{O}_{X,x})$

## Implementation notes

The proofs use order-preserving maps between posets of irreducible closed sets to establish
dimension inequalities. The key technical lemma shows that the closure operation provides
an injective strictly monotone map from irreducible closed sets of a subspace to those of
the ambient space.

## Tags

Krull dimension, topological dimension, schemes, irreducible components, dimension theory
-/

open Set Function Order TopologicalSpace AlgebraicGeometry

variable {X : Type*} [TopologicalSpace X]

/-! ### Maps between irreducible closed sets -/

/-- The canonical map from irreducible closed sets of a subspace `Y` to irreducible
closed sets of the ambient space `X`, defined by taking the closure of the image
under the inclusion map. This map is crucial for comparing Krull dimensions. -/
def mapIrreducibleClosed (Y : Set X) (c : IrreducibleCloseds Y) : IrreducibleCloseds X where
  carrier := closure (Subtype.val '' c.carrier)
  is_irreducible' := c.is_irreducible'.image Subtype.val
    (continuous_subtype_val.continuousOn) |>.closure
  is_closed' := isClosed_closure

/-- The map `mapIrreducibleClosed` is injective, meaning distinct irreducible
closed sets in a subspace map to distinct irreducible closed sets in the ambient space.
This ensures that the dimension-preserving properties hold. -/
lemma mapIrreducibleClosed_injective (Y : Set X) :
    Function.Injective (mapIrreducibleClosed Y) := by
  intro A B h_images_eq
  ext x
  have h_closures_eq : closure (Subtype.val '' A.carrier) =
      closure (Subtype.val '' B.carrier) :=
    congrArg IrreducibleCloseds.carrier h_images_eq
  constructor
  · -- Forward direction: x ∈ A → x ∈ B
    intro hx_in_A
    change x ∈ B.carrier
    -- Use the mathlib lemma for embeddings
    rw [← B.is_closed'.closure_eq,
        Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
        ← h_closures_eq]
    simp_rw [mem_preimage]
    exact subset_closure (mem_image_of_mem Subtype.val hx_in_A)
  · -- Backward direction: x ∈ B → x ∈ A
    intro hx_in_B
    change x ∈ A.carrier
    -- Use the mathlib lemma for embeddings
    rw [← A.is_closed'.closure_eq,
        Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
        h_closures_eq]
    simp_rw [mem_preimage]
    exact subset_closure (mem_image_of_mem Subtype.val hx_in_B)


/-! ### Partial order structure on irreducible closed sets -/

instance : PartialOrder (IrreducibleCloseds X) where
  le s t := s.carrier ⊆ t.carrier
  le_refl s := Set.Subset.refl _
  le_trans s t u hst htu := Set.Subset.trans hst htu
  le_antisymm s t hst hts := IrreducibleCloseds.ext (Set.Subset.antisymm hst hts)

/-- The partial order on `IrreducibleCloseds X` is given by subset inclusion
of the underlying sets. -/
lemma IrreducibleCloseds.le_iff_subset {s t : IrreducibleCloseds X} :
    s ≤ t ↔ s.carrier ⊆ t.carrier := by rfl

/-- The strict partial order on `IrreducibleCloseds X` corresponds to strict
subset inclusion of the underlying sets. -/
lemma IrreducibleCloseds.lt_iff_subset {s t : IrreducibleCloseds X} :
    s < t ↔ s.carrier ⊂ t.carrier := by
  constructor
  · intro h_lt
    have h_le := le_of_lt h_lt
    have h_ne := ne_of_lt h_lt
    rw [ssubset_iff_subset_ne]
    exact ⟨by rwa [← IrreducibleCloseds.le_iff_subset], mt IrreducibleCloseds.ext h_ne⟩
  · intro h_ssubset
    rw [lt_iff_le_and_ne]
    rcases h_ssubset with ⟨h_subset, h_ne_carrier⟩
    constructor
    · rwa [IrreducibleCloseds.le_iff_subset]
    · intro h_s_eq_t
      apply h_ne_carrier
      rw [h_s_eq_t]

/-- The canonical map `mapIrreducibleClosed` is strictly monotone, preserving
the order structure when comparing irreducible closed sets between subspaces
and ambient spaces. This is essential for the dimension inequality theorem. -/
lemma mapIrreducibleClosed_strictMono (Y : Set X) :
    StrictMono (mapIrreducibleClosed Y) := by
  intro A B h_less_AB
  constructor
  · -- Part 1: Prove map A ≤ map B
    apply closure_mono
    apply image_subset
    exact le_of_lt h_less_AB
  · -- Part 2: Prove ¬(map B ≤ map A)
    intro h_contra_le
    have h_forward_subset : (mapIrreducibleClosed Y A).carrier ⊆
        (mapIrreducibleClosed Y B).carrier := by
      apply closure_mono
      apply image_subset
      exact le_of_lt h_less_AB
    have h_carrier_eq : (mapIrreducibleClosed Y A).carrier = (mapIrreducibleClosed Y B).carrier :=
      Subset.antisymm h_forward_subset h_contra_le
    have h_A_eq_B : A = B :=
      mapIrreducibleClosed_injective Y (IrreducibleCloseds.ext h_carrier_eq)
    exact (ne_of_lt h_less_AB) h_A_eq_B

/-! ### Main dimension theorems -/

/-- **Subspace Dimension Inequality**: The topological Krull dimension of any subspace
is at most the dimension of the ambient space. This fundamental result shows that
subspaces cannot have larger dimension than their ambient space. -/
theorem topKrullDim_subspace_le (X : Type*) [TopologicalSpace X] (Y : Set X) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  unfold topologicalKrullDim
  exact krullDim_le_of_strictMono (mapIrreducibleClosed Y) (mapIrreducibleClosed_strictMono Y)

/-- **Proper Closed Subset Dimension**: A proper closed subset of an irreducible space
with finite dimension has strictly smaller topological Krull dimension. This is a
key result showing that proper closed subsets always have smaller dimension. -/
theorem topological_dim_proper_closed_subset_lt (X : Type*) [TopologicalSpace X]
  (Y : Set X) (hX_irred : IsIrreducible (Set.univ : Set X))
  (hX_finite : topologicalKrullDim X ≠ ⊤)
  (hY_closed : IsClosed Y)
  (hY_proper : Y ⊂ Set.univ)
  (hY_nonempty : Y.Nonempty) :
  topologicalKrullDim Y < topologicalKrullDim X := by
  apply lt_of_le_of_ne (topKrullDim_subspace_le X Y)
  intro h_dim_eq

  have h_dim_exists : ∃ n : ℕ∞, topologicalKrullDim X = ↑n := by
    apply Exists.imp (fun _ => Eq.symm)
    apply (WithBot.ne_bot_iff_exists).mp
    apply Order.krullDim_ne_bot_iff.mpr
    constructor
    let x := hY_nonempty.some
    exact {
      carrier := closure {x},
      is_irreducible' := isIrreducible_singleton.closure,
      is_closed' := isClosed_closure
    }

  obtain ⟨n, hn⟩ := h_dim_exists
  obtain ⟨m, hn_eq_m⟩ : ∃ m : ℕ, n = ↑m := by
    apply Exists.imp (fun _ => Eq.symm)
    apply WithTop.ne_top_iff_exists.mp
    intro hn_top
    rw [hn_top] at hn
    exact hX_finite hn

  have h_dim_Y_eq_m : topologicalKrullDim ↑Y = ↑m := by
    rw [h_dim_eq, hn, hn_eq_m]
    exact WithBot.coe_eq_coe.mpr (WithTop.coe_eq_coe.mpr rfl)

  have h_chain_Y_exists := (le_krullDim_iff.mp (le_of_eq h_dim_Y_eq_m.symm))
  obtain ⟨c, hc_chain⟩ := h_chain_Y_exists

  let c' := List.map (mapIrreducibleClosed Y) c.toList
  have hc'_chain : List.Chain' (· < ·) c' := by
    apply List.chain'_map_of_chain' (mapIrreducibleClosed Y)
    · exact mapIrreducibleClosed_strictMono Y
    · exact RelSeries.toList_chain' c

  let X_ics : IrreducibleCloseds X := ⟨Set.univ, hX_irred, isClosed_univ⟩
  have h_last_lt_X : List.getLast c' (by
      apply List.ne_nil_of_length_pos
      dsimp only [c']
      rw [List.length_map, RelSeries.length_toList, hc_chain]
      linarith) < X_ics := by

    let last_Y := c.last
    have h_last_eq : List.getLast c' (by
        apply List.ne_nil_of_length_pos
        simp [c', RelSeries.length_toList, hc_chain, List.length_map]
      ) = mapIrreducibleClosed Y last_Y := by
      rw [List.getLast_map]
      congr
      dsimp [last_Y]
      rw [List.getLast_eq_getElem]
      simp only [RelSeries.length_toList, hc_chain, Nat.add_one_sub_one]
      change (RelSeries.toList c).get ⟨m, ?_⟩ = RelSeries.last c
      simp only [RelSeries.toList, List.get_ofFn, RelSeries.last]
      congr
      apply Fin.eq_of_val_eq
      simp [hc_chain]

    rw [h_last_eq, IrreducibleCloseds.lt_iff_subset]
    change (closure (Subtype.val '' c.last.carrier)) ⊂ X_ics.carrier
    have h_carrier_closed_in_X : IsClosed (Subtype.val '' c.last.carrier) :=
      IsClosed.isClosedMap_subtype_val hY_closed _ c.last.is_closed'
    rw [h_carrier_closed_in_X.closure_eq]
    have h_subset_Y : Subtype.val '' c.last.carrier ⊆ Y := by
      rintro _ ⟨y, _, rfl⟩; exact y.property
    exact ssubset_of_subset_of_ssubset h_subset_Y hY_proper

  let extended_chain := c' ++ [X_ics]
  have h_extended_chain : List.Chain' (· < ·) extended_chain := by
    apply List.Chain'.append
    · exact hc'_chain
    · simp
    · intro last_val h_last_mem first_val h_first_mem
      have h_c'_ne_nil : c' ≠ [] := by
        apply List.ne_nil_of_length_pos
        simp only [c', List.length_map, RelSeries.length_toList, hc_chain]
        linarith
      rw [List.getLast?_eq_getLast h_c'_ne_nil, Option.mem_some_iff] at h_last_mem
      rw [List.head?_cons, Option.mem_some_iff] at h_first_mem
      rw [← h_last_mem, ← h_first_mem]
      exact h_last_lt_X

  have h_new_chain_len : extended_chain.length = m + 2 := by
    simp [extended_chain, c', List.length_append, List.length_singleton,
      List.length_map, RelSeries.length_toList, hc_chain]

  have h_dim_ge_m_plus_1 : ↑(m + 1) ≤ topologicalKrullDim X := by
    unfold topologicalKrullDim
    rw [le_krullDim_iff]
    have h_extended_chain_ne_nil : extended_chain ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [h_new_chain_len]
      linarith
    use RelSeries.fromListChain' extended_chain h_extended_chain_ne_nil h_extended_chain
    simp [h_new_chain_len]

  rw [← h_dim_eq, h_dim_Y_eq_m] at h_dim_ge_m_plus_1
  norm_cast at h_dim_ge_m_plus_1
  linarith

/-! ### Helper lemmas for open cover theorem -/

/-- If the topological space `X` is empty, then the type `IrreducibleCloseds X`
of irreducible closed subsets is also empty. This handles the degenerate case
for dimension calculations. -/
lemma IrreducibleCloseds.isEmpty_of_isEmpty {X : Type*} [TopologicalSpace X]
    (h : IsEmpty X) : IsEmpty (IrreducibleCloseds X) := by
  constructor
  intro ic
  have h_nonempty : ic.carrier.Nonempty := IsIrreducible.nonempty ic.is_irreducible'
  have h_empty_carrier : ic.carrier = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro x hx
    exact IsEmpty.elim h x
  rw [h_empty_carrier] at h_nonempty
  exact Set.not_nonempty_empty h_nonempty

/-- If the first (smallest) set in an increasing chain of irreducible closed sets
intersects an open set `U`, then all sets in the chain intersect `U`. This uses
the monotonicity of the chain. -/
lemma nonempty_inter_of_chain {X : Type*} [TopologicalSpace X]
    (c : LTSeries (IrreducibleCloseds X)) (U : Set X)
    (h_int_zero : ((c.toFun 0).carrier ∩ U).Nonempty) (i : Fin (c.length + 1)) :
    ((c.toFun i).carrier ∩ U).Nonempty := by
  have h_subset : (c.toFun 0).carrier ⊆ (c.toFun i).carrier := by
    have h_mono : Monotone c.toFun := (Fin.strictMono_iff_lt_succ.mpr c.step).monotone
    exact h_mono (Fin.zero_le i)
  exact Set.Nonempty.mono (inter_subset_inter h_subset fun ⦃a⦄ a ↦ a) h_int_zero

/-- Given a chain of irreducible closed sets in the ambient space `X` where the
first set intersects an open set `U`, we can construct a corresponding chain of
the same length in the subspace `U`. This is crucial for the open cover theorem. -/
lemma chain_restriction_to_open_cover {X : Type*} [TopologicalSpace X]
    (c : LTSeries (IrreducibleCloseds X)) (U : Set X) (hU : IsOpen U)
    (h_int : ((c.toFun 0).carrier ∩ U).Nonempty) :
    ∃ d : LTSeries (IrreducibleCloseds ↑U), d.length = c.length := by

  let d_fun (i : Fin (c.length + 1)) : IrreducibleCloseds U := {
    carrier := Subtype.val ⁻¹' (c.toFun i).carrier,
    is_irreducible' := by
      constructor
      · rw [Subtype.preimage_coe_nonempty, Set.inter_comm U]
        exact nonempty_inter_of_chain c U h_int i
      · apply IsPreirreducible.preimage
        · exact (c.toFun i).is_irreducible'.isPreirreducible
        · exact IsOpen.isOpenEmbedding_subtypeVal hU
    is_closed' := (c.toFun i).is_closed'.preimage continuous_subtype_val
  }

  have h_strict_mono : StrictMono d_fun := by
    intro i j h_lt_ij
    simp_rw [IrreducibleCloseds.lt_iff_subset, d_fun]
    let Zᵢ := (c.toFun i).carrier
    let Zⱼ := (c.toFun j).carrier
    have h_c_mono : StrictMono c.toFun := Fin.strictMono_iff_lt_succ.mpr c.step
    have h_lt_Z : c.toFun i < c.toFun j := h_c_mono h_lt_ij
    have h_Z_ssubset : Zᵢ ⊂ Zⱼ := IrreducibleCloseds.lt_iff_subset.mp h_lt_Z
    rw [ssubset_iff_subset_ne]
    constructor
    · rw [Subtype.preimage_val_subset_preimage_val_iff]
      refine inter_subset_inter_right U ?_
      exact subset_of_ssubset (h_c_mono h_lt_ij)
    · intro h_inter_eq
      have h_nonempty_inter_U : (Zⱼ ∩ U).Nonempty :=
        nonempty_inter_of_chain c U h_int j
      have h_nonempty_inter_compl_Zᵢ : (Zⱼ \ Zᵢ).Nonempty :=
        nonempty_of_ssubset h_Z_ssubset
      have h_triple_inter_nonempty : (Zⱼ ∩ (compl Zᵢ ∩ U)).Nonempty :=
        (c.toFun j).is_irreducible'.isPreirreducible (compl Zᵢ) U
          (isOpen_compl_iff.mpr (c.toFun i).is_closed') hU
          h_nonempty_inter_compl_Zᵢ h_nonempty_inter_U
      have h_inter_empty : (Zⱼ \ Zᵢ) ∩ U = ∅ := by
        rw [Set.diff_eq_compl_inter, Set.inter_assoc, Set.inter_comm]
        rw [Subtype.preimage_coe_eq_preimage_coe_iff, Set.inter_comm U _,
          Set.inter_comm U _] at h_inter_eq
        change Zᵢ ∩ U = Zⱼ ∩ U at h_inter_eq
        rw [← h_inter_eq, Set.inter_assoc, Set.inter_comm, Set.inter_assoc]
        simp only [compl_inter_self, inter_empty, d_fun]
      simp only [Set.inter_assoc, Set.diff_eq_compl_inter] at h_inter_empty
      rw [inter_left_comm] at h_inter_empty
      exact h_triple_inter_nonempty.ne_empty h_inter_empty

  use {
    length := c.length,
    toFun := d_fun,
    step := by
      intro i
      apply h_strict_mono
      simp only [Fin.castSucc_lt_succ_iff, le_refl, d_fun]
  }


/-- **Open Cover Dimension**: The topological Krull dimension of a space equals
the supremum of dimensions over any open cover. This fundamental result allows
computing dimensions by covering the space with simpler open sets. -/
theorem topological_dim_open_cover (X : Type*) [TopologicalSpace X]
  (ι : Type*) (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ) :
  topologicalKrullDim X = ⨆ i, topologicalKrullDim (U i) := by

  by_cases h_empty : IsEmpty X
  · -- Case: X is empty
    have h_U_empty : ∀ i, IsEmpty (U i) := by
      intro i
      have hU_subset_X : U i ⊆ (Set.univ : Set X) := Set.subset_univ _
      have h_univ_empty : (Set.univ : Set X) = ∅ := by
        apply Set.eq_empty_of_isEmpty
      rw [h_univ_empty, Set.subset_empty_iff] at hU_subset_X
      apply Set.isEmpty_coe_sort.mpr
      exact hU_subset_X

    have h_X_empty_krull : topologicalKrullDim X = ⊥ := by
      unfold topologicalKrullDim
      have ic_X_empty : IsEmpty (IrreducibleCloseds X) :=
        IrreducibleCloseds.isEmpty_of_isEmpty h_empty
      rw [krullDim_eq_bot]

    have h_U_empty_krull : ⨆ i, topologicalKrullDim ↑(U i) = ⊥ := by
      unfold topologicalKrullDim
      have ic_U_empty : ∀ i, IsEmpty (IrreducibleCloseds ↑(U i)) := by
        intro i
        exact IrreducibleCloseds.isEmpty_of_isEmpty (h_U_empty i)
      rw [iSup_eq_bot]
      intro i
      rw [krullDim_eq_bot]
    rw [h_X_empty_krull, h_U_empty_krull]

  -- Case: X is nonempty
  · rw [not_isEmpty_iff] at h_empty
    unfold topologicalKrullDim

    have h_irreducible_nonempty : Nonempty (IrreducibleCloseds X) := by
      constructor
      let x := h_empty.some
      exact {
        carrier := closure {x},
        is_irreducible' := isIrreducible_singleton.closure,
        is_closed' := isClosed_closure
      }

    have h_exists_nonempty_U : ∃ i, Nonempty ↑(U i) := by
      by_contra h_all_empty
      push_neg at h_all_empty
      have h_union_empty : ⋃ i, U i = ∅ := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
        intro ⟨j, hx_in_Uj⟩
        exact h_all_empty j ⟨⟨x, hx_in_Uj⟩⟩
      rw [h_union_empty] at hcover
      have empty_X : IsEmpty X := by
        rw [← Set.univ_eq_empty_iff]
        symm at hcover
        exact hcover
      exact empty_X.elim h_empty.some

    apply le_antisymm
    · -- First direction: dim X ≤ supᵢ dim Uᵢ
      rw [le_iSup_iff]
      intro b h_b_is_upper_bound
      apply iSup_le
      intro c
      have h_first_intersects : ∃ i, ((c.toFun 0).carrier ∩ U i).Nonempty := by
        have h_nonempty : (c.toFun 0).carrier.Nonempty := (c.toFun 0).is_irreducible'.nonempty
        have h_subset : (c.toFun 0).carrier ⊆ ⋃ i, U i := by
          rw [hcover]
          exact Set.subset_univ _
        obtain ⟨x, hx_in_first⟩ := h_nonempty
        have hx_in_union : x ∈ ⋃ i, U i := h_subset hx_in_first
        obtain ⟨i₀, hx_in_Ui₀⟩ := Set.mem_iUnion.mp hx_in_union
        exact ⟨i₀, ⟨x, hx_in_first, hx_in_Ui₀⟩⟩
      obtain ⟨i₀, h_int⟩ := h_first_intersects
      obtain ⟨d, hd_len⟩ :
        ∃ d : LTSeries (IrreducibleCloseds ↑(U i₀)), d.length = c.length :=
        chain_restriction_to_open_cover c (U i₀) (hU i₀) h_int
      calc (c.length : WithBot ℕ∞)
          = (d.length : WithBot ℕ∞)      := by rw [hd_len]
        _ ≤ topologicalKrullDim ↑(U i₀) := LTSeries.length_le_krullDim d
        _ ≤ b                           := h_b_is_upper_bound i₀
    · -- Show ⨆ i, krullDim (U i) ≤ krullDim X
      apply iSup_le
      intro i
      exact topKrullDim_subspace_le X (U i)

/-! ### Helper lemma for irreducible components theorem -/
/-- A maximal preirreducible set is an irreducible component. This lemma establishes
the connection between the abstract notion of maximality and the concrete definition
of irreducible components. -/
lemma maximal_preirreducible_is_irred_component {t : Set X} (h_nonempty : t.Nonempty)
    (h_preirred : IsPreirreducible t)
    (h_maximal : ∀ u, IsPreirreducible u → t ⊆ u → u = t) :
    t ∈ irreducibleComponents X := by
  have h_irred : IsIrreducible t := ⟨h_nonempty, h_preirred⟩
  refine ⟨h_irred, ?_⟩
  intro u h_u_irred h_t_subset_u
  simp only [le_eq_subset] at h_t_subset_u ⊢
  have h_u_t : u = t := h_maximal u h_u_irred.isPreirreducible h_t_subset_u
  rw [h_u_t]

/-- **Irreducible Components Dimension**: The topological Krull dimension equals
the supremum over all irreducible components. This shows that the dimension is
completely determined by the dimensions of the irreducible components. -/
theorem topological_dim_irreducible_components (X : Type*) [TopologicalSpace X] :
    topologicalKrullDim X = ⨆ (Y ∈ irreducibleComponents X), topologicalKrullDim Y := by
  unfold topologicalKrullDim
  apply le_antisymm
  · -- Direction 1: dim X ≤ sup_{Y ∈ Components} dim Y
    apply iSup_le
    intro c
    let Z_last := c.last
    have h_Z_last_irred : IsIrreducible Z_last.carrier := Z_last.is_irreducible'
    obtain ⟨Y_comp, h_Y_preirred, h_Z_subset_Y, h_Y_maximal⟩ :=
      exists_preirreducible Z_last.carrier h_Z_last_irred.isPreirreducible
    have hY_comp_in_components : Y_comp ∈ irreducibleComponents X := by
      have h_nonempty : Y_comp.Nonempty := Nonempty.mono h_Z_subset_Y h_Z_last_irred.nonempty
      exact maximal_preirreducible_is_irred_component h_nonempty h_Y_preirred h_Y_maximal
    have h_chain_in_Y : ∀ i, (c.toFun i).carrier ⊆ Y_comp := by
      intro i
      have h_mono : Monotone c.toFun := (Fin.strictMono_iff_lt_succ.mpr c.step).monotone
      exact Subset.trans (h_mono (Fin.le_last i)) h_Z_subset_Y
    have h_len_le_dim_Y : (c.length : WithBot ℕ∞) ≤ krullDim (IrreducibleCloseds ↑Y_comp) := by
      let d_fun (i : Fin (c.length + 1)) : IrreducibleCloseds Y_comp := {
        carrier := {y : Y_comp | y.val ∈ (c.toFun i).carrier},
        is_irreducible' := by
          constructor
          · have h_nonempty : (c.toFun i).carrier.Nonempty := (c.toFun i).is_irreducible'.nonempty
            obtain ⟨x, hx_in_Zi⟩ := h_nonempty
            have hx_in_Y : x ∈ Y_comp := h_chain_in_Y i hx_in_Zi
            exact ⟨⟨x, hx_in_Y⟩, hx_in_Zi⟩
          · intro u v hu hv h_nonempty_u h_nonempty_v
            let Z_i := (c.toFun i).carrier
            let d_carrier := {y : Y_comp | y.val ∈ Z_i}
            obtain ⟨U, hU_open, rfl⟩ := isOpen_induced_iff.mp hu
            obtain ⟨V, hV_open, rfl⟩ := isOpen_induced_iff.mp hv
            have h_nonempty_U_in_X : (Z_i ∩ U).Nonempty :=
              nonempty_of_nonempty_preimage h_nonempty_u
            have h_nonempty_V_in_X : (Z_i ∩ V).Nonempty :=
              nonempty_of_nonempty_preimage h_nonempty_v
            have h_inter_nonempty_in_X :=
              (c.toFun i).is_irreducible'.isPreirreducible U V hU_open hV_open
                h_nonempty_U_in_X h_nonempty_V_in_X
            obtain ⟨x, hx_in_inter⟩ := h_inter_nonempty_in_X
            have hx_in_Z_i : x ∈ Z_i := hx_in_inter.1
            have hx_in_U_and_V : x ∈ U ∩ V := hx_in_inter.2
            have hx_in_Y_comp : x ∈ Y_comp := (h_chain_in_Y i) hx_in_Z_i
            let y : Y_comp := ⟨x, hx_in_Y_comp⟩
            use y
            exact ⟨hx_in_Z_i, hx_in_U_and_V.1, hx_in_U_and_V.2⟩
        is_closed' := (c.toFun i).is_closed'.preimage continuous_subtype_val
      }
      have h_d_strict_mono : StrictMono d_fun := by
        intro i j h_lt
        rw [IrreducibleCloseds.lt_iff_subset, ssubset_iff_subset_ne]
        constructor
        · change (Subtype.val ⁻¹' (c.toFun i).carrier) ⊆ (Subtype.val ⁻¹' (c.toFun j).carrier)
          have h_c_lt := (Fin.strictMono_iff_lt_succ.mpr c.step) h_lt
          have h_c_subset : (c.toFun i).carrier ⊆ (c.toFun j).carrier := le_of_lt h_c_lt
          exact Set.preimage_mono h_c_subset
        · intro h_eq
          have h_carriers_eq : (c.toFun i).carrier = (c.toFun j).carrier := by
            apply (preimage_eq_preimage' _ _).mp h_eq
            · rw [Subtype.range_val]
              exact h_chain_in_Y i
            · rw [Subtype.range_val]
              exact h_chain_in_Y j
          have h_c_lt := (Fin.strictMono_iff_lt_succ.mpr c.step) h_lt
          have h_c_ne := ne_of_lt h_c_lt
          apply h_c_ne
          exact IrreducibleCloseds.ext h_carriers_eq
      let d : LTSeries (IrreducibleCloseds Y_comp) := {
        toFun := d_fun,
        step := fun i => h_d_strict_mono (by simp : Fin.castSucc i < Fin.succ i),
        length := c.length
      }
      convert LTSeries.length_le_krullDim d
    have h_dim_le_sup : krullDim (IrreducibleCloseds ↑Y_comp) ≤
        ⨆ (Y ∈ irreducibleComponents X), krullDim (IrreducibleCloseds ↑Y) := by
      let f := fun (Y : Set X) => krullDim (IrreducibleCloseds ↑Y)
      let S := irreducibleComponents X
      rw [← sSup_image]
      change f Y_comp ≤ sSup (f '' S)
      have h_bdd_above : BddAbove (f '' S) := by
        use krullDim (IrreducibleCloseds X)
        rintro _ ⟨Y, hY_mem, rfl⟩
        exact topKrullDim_subspace_le X Y
      have h_mem : f Y_comp ∈ f '' S :=
        mem_image_of_mem f hY_comp_in_components
      exact le_csSup h_bdd_above h_mem
    exact le_trans h_len_le_dim_Y h_dim_le_sup
  · -- Direction 2: sup_{Y ∈ Components} dim Y ≤ dim X
    apply iSup₂_le
    intro Y hY
    exact topKrullDim_subspace_le X Y

/-! ### Scheme dimension -/

/-- The dimension of a scheme is defined as the Krull dimension of its underlying
topological space. This connects the algebraic geometry notion of scheme dimension
with the topological Krull dimension. -/
noncomputable def schemeDim (X : Scheme) : WithBot ℕ∞ :=
  topologicalKrullDim X.carrier

/-- **Scheme Dimension via Local Rings**: For any scheme `X`, the dimension equals
the supremum of Krull dimensions of stalks `X.presheaf.stalk x` at all points `x`.
This fundamental result connects the geometric dimension with algebraic invariants. -/
theorem scheme_dim_eq_sup_local_rings (X : Scheme) :
    schemeDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x) := by
  let 𝒰 := X.affineCover
  unfold schemeDim
  rw [topological_dim_open_cover X.carrier 𝒰.J
      (fun i ↦ Set.range (𝒰.map i).base)
      (fun i ↦ IsOpenImmersion.isOpen_range (𝒰.map i))
      𝒰.iUnion_range]

  have h_rhs_sup : (⨆ x : X, ringKrullDim (X.presheaf.stalk x)) =
      ⨆ (i : 𝒰.J), ⨆ (x : Set.range (𝒰.map i).base),
        ringKrullDim (X.presheaf.stalk x) := by
    rw [← iSup_univ, ← 𝒰.iUnion_range, iSup_iUnion]
    apply iSup_congr
    intro i
    let U_opens : Opens X.carrier := (𝒰.map i).opensRange
    rw [iSup_subtype']

  rw [h_rhs_sup]
  apply iSup_congr
  intro i
  let f := 𝒰.map i
  haveI : IsOpenImmersion f := 𝒰.map_prop i
  let Y := 𝒰.obj i
  let e_scheme : Y ≅ (f.opensRange : Scheme) := Scheme.Hom.isoOpensRange f
  let e_homeo : Y.carrier ≃ₜ ↑(f.opensRange) :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e_scheme)
  have dim_eq : topologicalKrullDim (Set.range f.base) = topologicalKrullDim Y.carrier :=
    (IsHomeomorph.topologicalKrullDim_eq e_homeo e_homeo.isHomeomorph).symm
  rw [dim_eq]
  have rhs_eq : (⨆ x : ↥(Set.range f.base), ringKrullDim (X.presheaf.stalk x.val)) =
      (⨆ y : Y.carrier, ringKrullDim (X.presheaf.stalk (e_homeo y).val)) := by
    rw [← Scheme.Hom.coe_opensRange]
    apply le_antisymm
    · apply iSup_le
      intro x
      convert le_iSup (fun y' => ringKrullDim (X.presheaf.stalk (e_homeo y').val))
        (e_homeo.symm x)
      rw [Homeomorph.apply_symm_apply]
    · apply iSup_le
      intro y
      convert le_iSup (fun x' => ringKrullDim (X.presheaf.stalk x'.val))
        (e_homeo y)
  rw [rhs_eq]
  change schemeDim Y = _
  let R := Scheme.Γ.obj (Opposite.op Y)
  let R_iso_spec : Y ≅ Spec (Scheme.Γ.obj (Opposite.op Y)) :=
    Scheme.isoSpec Y
  unfold schemeDim
  let h_homeo : Y.carrier ≃ₜ (Spec (Scheme.Γ.obj (Opposite.op Y))).carrier :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso R_iso_spec)
  rw [IsHomeomorph.topologicalKrullDim_eq h_homeo h_homeo.isHomeomorph]
  change topologicalKrullDim (PrimeSpectrum (Scheme.Γ.obj (Opposite.op Y))) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  let h_homeo_affine : Y.carrier ≃ₜ (Spec R).carrier :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso R_iso_spec)
  rw [eq_comm]
  calc
    ⨆ y, ringKrullDim (X.presheaf.stalk (e_homeo y).val)
    _ = ⨆ y, ringKrullDim (Y.presheaf.stalk y) := by
      apply iSup_congr; intro y
      have h_point_eq : (e_homeo y).val = f.base y :=
        congr_fun (congr_arg (fun g => g.base)
          (Scheme.Hom.isoOpensRange_hom_ι f)) y
      rw [h_point_eq]
      exact RingEquiv.ringKrullDim (CategoryTheory.Iso.commRingCatIsoToRingEquiv
        (CategoryTheory.asIso (f.stalkMap y)))
    _ = ⨆ p : PrimeSpectrum R, ringKrullDim ((Spec R).presheaf.stalk p) := by
      have h_sup_eq : (⨆ y, ringKrullDim (Y.presheaf.stalk y)) =
          (⨆ y, ringKrullDim ((Spec R).presheaf.stalk (h_homeo_affine y))) := by
        apply iSup_congr; intro y
        let stalk_map := (R_iso_spec.hom).stalkMap y
        let stalk_equiv := CategoryTheory.Iso.commRingCatIsoToRingEquiv
          (CategoryTheory.asIso stalk_map)
        exact (RingEquiv.ringKrullDim stalk_equiv.symm)
      rw [h_sup_eq]
      rw [h_homeo_affine.toEquiv.iSup_congr]
      rfl
      exact fun x ↦ rfl
    _ = ⨆ p : PrimeSpectrum R, ringKrullDim (Localization.AtPrime p.asIdeal) := by
      apply iSup_congr; intro p
      let stalk_iso := AlgebraicGeometry.StructureSheaf.stalkIso R p
      let stalk_equiv := CategoryTheory.Iso.commRingCatIsoToRingEquiv stalk_iso
      exact RingEquiv.ringKrullDim stalk_equiv
    _ = ringKrullDim R := by
      cases isEmpty_or_nonempty (PrimeSpectrum R)
      · case inl h_empty =>
          haveI : IsEmpty (PrimeSpectrum R) := h_empty
          rw [iSup_of_empty]
          rw [ringKrullDim, krullDim_eq_bot]
      · case inr h_nonempty =>
          haveI : Nonempty (PrimeSpectrum R) := h_nonempty
          apply Eq.symm
          rw [ringKrullDim, Order.krullDim_eq_iSup_height]
          apply iSup_congr
          intro p
          have h_dim_eq_height :
            ringKrullDim (Localization.AtPrime p.asIdeal) = p.asIdeal.height := by
            apply IsLocalization.AtPrime.ringKrullDim_eq_height
          rw [h_dim_eq_height]
          rw [Ideal.height_eq_primeHeight, Ideal.primeHeight]

/-! ### Combined main theorem -/

/-- **Main Theorem**: Combined statement of all dimension results. This theorem
packages together all the fundamental results about topological Krull dimension:
- Subspace dimension inequality
- Proper closed subset dimension strictness
- Open cover dimension formula
- Irreducible components dimension formula
- Scheme dimension via local rings

These results form the foundation of dimension theory in algebraic geometry. -/
theorem thm_scheme_dim :
  (∀ (X : Type*) [TopologicalSpace X] (Y : Set X),
    topologicalKrullDim Y ≤ topologicalKrullDim X) ∧
  (∀ (X : Type*) [TopologicalSpace X] (Y : Set X),
    IsIrreducible (Set.univ : Set X) →
    topologicalKrullDim X ≠ ⊤ →
    IsClosed Y → Y ⊂ Set.univ → Y.Nonempty →
    topologicalKrullDim Y < topologicalKrullDim X) ∧
  (∀ (X : Type*) [TopologicalSpace X] (ι : Type*) (U : ι → Set X),
    (∀ i, IsOpen (U i)) → (⋃ i, U i = Set.univ) →
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (U i)) ∧
  (∀ (X : Type*) [TopologicalSpace X],
    topologicalKrullDim X =
      ⨆ (Y ∈ irreducibleComponents X), topologicalKrullDim Y) ∧
  (∀ (X : Scheme), schemeDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x)) := by
  exact ⟨topKrullDim_subspace_le, topological_dim_proper_closed_subset_lt,
         topological_dim_open_cover, topological_dim_irreducible_components,
         scheme_dim_eq_sup_local_rings⟩
