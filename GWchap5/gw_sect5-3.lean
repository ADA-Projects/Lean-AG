import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Closure
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Irreducible
import Mathlib.Data.Set.Image
import Mathlib.Order.SuccPred.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.RelIso.Basic -- For OrderIso -- For properties of PrimeSpectrum
import Mathlib.Geometry.RingedSpace.OpenImmersion
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.RingTheory.Ideal.Height

open Set Function

open Order TopologicalSpace AlgebraicGeometry Set

variable {X : Type*} [TopologicalSpace X]

lemma closure_in_subspace_eq_inter (Y : Set X) (A : Set Y) :
    closure A = Subtype.val ⁻¹' closure (Subtype.val '' A) := by
  ext y
  -- Use `simp_rw` to unfold the definition of closure on both sides of the iff.
  -- This is more robust than multiple `rw` calls.
  --simp_rw [mem_closure_iff, mem_preimage]
  constructor

  · -- Forward direction: `y ∈ closure A → ↑y ∈ closure (↑ '' A)`
    -- Assume `y` is in the closure of `A` (in the subspace `Y`).
    intro hy_closure
    simp_rw [mem_preimage, mem_closure_iff]
    -- Let V be an open neighborhood of ↑y in X.
    intro V hV_open hy_in_V
    rw [mem_closure_iff] at hy_closure
     -- We must show V intersects ↑ '' A.
    have hVA_nonempty : ((↑)⁻¹' V ∩ A).Nonempty :=
      hy_closure (Subtype.val ⁻¹' V) (isOpen_induced_iff.mpr ⟨V, hV_open, rfl⟩) hy_in_V
    -- hVA_nonempty guarantees there's a point `z` in the intersection. Let's get it.
    obtain ⟨z, hz_in_preimage, hz_in_A⟩ := hVA_nonempty

    -- Now, use the image of `z` to prove the goal.
    use Subtype.val z -- or just `use ↑z`
    constructor
    · -- Goal 1: Prove `↑z ∈ V`
      -- This is true because `z ∈ Subtype.val ⁻¹' V`
      exact hz_in_preimage
    · -- Goal 2: Prove `↑z ∈ Subtype.val '' A`
      -- This is true because `z ∈ A`
      exact mem_image_of_mem Subtype.val hz_in_A

  · -- Backward direction: `↑y ∈ closure (↑ '' A) → y ∈ closure A`
    intro hy_val_in_closure

    -- First, unfold our GOAL to the open neighborhood definition.
    rw [mem_closure_iff]

    -- Now, introduce an arbitrary open neighborhood U of y in the subspace Y.
    intro U hU_open hy_in_U

    -- As before, U is the preimage of some open set V in X.
    obtain ⟨V, hV_open_in_X, rfl⟩ := isOpen_induced_iff.mp hU_open
    have hy_in_V : ↑y ∈ V := hy_in_U

    -- This is the key step. We apply the neighborhood definition to our
    -- hypothesis `hy_val_in_closure` and give it the neighborhood V.
    have nonempty_inter := (mem_closure_iff.mp hy_val_in_closure) V hV_open_in_X hy_in_V

    -- `nonempty_inter` is now a proof that `(V ∩ ↑ '' A).Nonempty`.
    -- The rest of the proof is to unpack this and prove our goal.
    obtain ⟨x, ⟨hx_in_V, hx_in_image⟩⟩ := nonempty_inter
    obtain ⟨z, hz_in_A, rfl⟩ := hx_in_image

    -- We use the point z to show that U intersects A.
    use z
    -- The goal splits into two parts: `z ∈ U` and `z ∈ A`.
    -- `z ∈ A` is `hz_in_A`.
    -- `z ∈ U` is true because `↑z` is in `V`, and `U` is the preimage of `V`.
    exact ⟨hx_in_V, hz_in_A⟩


/- "correct" signature variant of the lemma above

lemma closed_in_subspace_eq_inter_var (Y : Set X) (A : Set ↥Y) (hA : IsClosed A) :
    (↑) '' A = Y ∩ closure ((↑) '' A) := by
  ext x
  constructor
  · -- Forward direction: `x ∈ image A → x ∈ Y ∩ closure (image A)`
    rintro ⟨y, hyA, rfl⟩
    exact ⟨y.property, subset_closure (mem_image_of_mem _ hyA)⟩

  · -- Backward direction: `x ∈ Y ∩ closure (image A) → x ∈ image A`
    rintro ⟨hxY, hx_closure⟩
    -- We need to show `∃ y ∈ A, ↑y = x`. The candidate is `y := ⟨x, hxY⟩`.
    use ⟨x, hxY⟩
    constructor
    · -- Goal 1: Prove `⟨x, hxY⟩ ∈ A`.
      -- Since A is closed in Y, it is equal to its closure in Y.
      rw [← hA.closure_eq]
      -- Now we use your first lemma to relate the closure in Y to the closure in X.
      rw [closure_in_subspace_eq_inter]
      -- The goal is now to prove `⟨x, hxY⟩` is in the preimage of the X-closure.
      -- By definition of preimage, this is the same as proving `x` is in the X-closure.
      exact hx_closure
    · -- Goal 2: Prove `↑⟨x, hxY⟩ = x`. This is true by definition.
      rfl

-/


lemma closed_in_subspace_eq_closure_inter (Y : Set X) (A : Set Y) (hA : IsClosed A) :
    (↑) '' A = (Y : Set X) ∩ closure ((↑) '' A) := by
  -- Prove equality by showing each side is a subset of the other.
  -- Or, more directly, prove membership is equivalent for any element x.
  ext x
  constructor

  · -- Forward direction: `x ∈ (↑) '' A → x ∈ Y ∧ x ∈ closure ((↑) '' A)`
    intro h_x_in_image
    -- Unpack the hypothesis: `h_x_in_image` means `x` is the image of some `y` in `A`.
    rcases h_x_in_image with ⟨y, hy_in_A, rfl⟩ -- rfl substitutes `x` with `↑y` everywhere

    -- Now we have two goals: `↑y ∈ Y` and `↑y ∈ closure ((↑) '' A)`
    constructor
    · -- Goal 1: Prove `↑y ∈ Y`. This is true by definition of the subtype Y.
      exact y.property
    · -- Goal 2: Prove `↑y ∈ closure ((↑) '' A)`.
      -- Apply the fact that any set is a subset of its closure.
      apply subset_closure
      -- Now, the goal is to prove that `↑y` is in the set itself.
      exact mem_image_of_mem Subtype.val hy_in_A

  · -- Backward direction: `x ∈ Y ∧ x ∈ closure ((↑) '' A) → x ∈ (↑) '' A`
    intro ⟨hx_in_Y, hx_in_closure⟩
    -- We have `x ∈ Y` and `x` is in the closure of the image of `A`.
    -- We want to show `x ∈ (↑) '' A`.

    -- The key is using the fact that A is closed.
    -- `hA : IsClosed A` means `closure A = A`.
    have h_closure_eq_A : closure A = A := hA.closure_eq

    -- Now, use our previous lemma to relate this to the closure in X.
    have h_preimage_eq_A : Subtype.val ⁻¹' closure (Subtype.val '' A) = A := by
      rw [← closure_in_subspace_eq_inter, h_closure_eq_A]

    -- We need to show `x ∈ (↑) '' A`. This means `∃ y ∈ A, ↑y = x`.
    -- Let's use the point `⟨x, hx_in_Y⟩`, which is an element of the subtype Y.
    use ⟨x, hx_in_Y⟩
    -- The goal is now two-fold: `⟨x, hx_in_Y⟩ ∈ A` and `↑⟨x, hx_in_Y⟩ = x`.
    constructor
    · -- Goal 1: Prove `⟨x, hx_in_Y⟩ ∈ A`.
      -- We can prove this by rewriting with our `h_preimage_eq_A` lemma.
      rw [← h_preimage_eq_A]
      -- The goal is now `⟨x, hx_in_Y⟩ ∈ Subtype.val ⁻¹' ...`,
      -- which is definitionally `↑⟨x, hx_in_Y⟩ ∈ closure...`
      -- which simplifies to `x ∈ closure...`, which is our hypothesis `hx_in_closure`.
      exact hx_in_closure
    · -- Goal 2: Prove `↑⟨x, hx_in_Y⟩ = x`. This is true by definition.
      rfl


/- The map from irreducible closed sets of a subspace to irreducible closed sets of the ambient space,
by taking the closure. --/
def map_irreducible_closed (Y : Set X) (c : IrreducibleCloseds Y) : IrreducibleCloseds X where
  carrier := closure (Subtype.val '' c.carrier)
  is_irreducible' := c.is_irreducible'.image Subtype.val (continuous_subtype_val.continuousOn) |>.closure
  is_closed' := isClosed_closure



lemma map_irreducible_closed_injective (Y : Set X) :
    Function.Injective (map_irreducible_closed Y) := by
  intro A B h_images_eq
  -- To prove A = B, by extensionality, it's enough to prove their carriers are equal.
  ext x

  -- From h_images_eq, we know the closures of the images in the ambient space X are equal.
  have h_closures_eq : closure (Subtype.val '' A.carrier) = closure (Subtype.val '' B.carrier) :=
    congrArg IrreducibleCloseds.carrier h_images_eq

  constructor
  · -- Forward direction: `x ∈ ↑A → x ∈ ↑B`
    intro hx_in_A

    -- The goal is `x ∈ ↑B`. Let's make the `.carrier` explicit using `change`.
    change x ∈ B.carrier

    -- Now that `B.carrier` is explicit, the rewrite will work.
    -- Since B is a closed set, proving `x ∈ B.carrier` is the same as proving `x` is in its closure.
    rw [← B.is_closed'.closure_eq]

    -- Now, use your helper lemma to relate the closure in Y to the closure in X.
    rw [closure_in_subspace_eq_inter]

    -- The goal is now `↑x ∈ closure (↑ '' B.carrier)`.
    -- We can use our hypothesis that the closures are equal to switch from B to A.
    rw [← h_closures_eq]

    -- The goal is now `↑x ∈ closure (↑ '' A.carrier)`.
    -- This is true because `x` is in `A`, so `↑x` is in the image of `A`,
    -- and any set is a subset of its closure.
    apply subset_closure
    exact mem_image_of_mem Subtype.val hx_in_A
  · -- Backward direction: `x ∈ ↑B → x ∈ ↑A`
    intro hx_in_B

    -- The goal is `x ∈ ↑A`. Let's make the `.carrier` explicit using `change`.
    change x ∈ A.carrier

    -- Now that `A.carrier` is explicit, the rewrite will work.
    -- Since A is a closed set, proving `x ∈ A.carrier` is the same as proving `x` is in its closure.
    rw [← A.is_closed'.closure_eq]

    -- Now, use your helper lemma to relate the closure in Y to the closure in X.
    rw [closure_in_subspace_eq_inter]

    -- The goal is now `↑x ∈ closure (↑ '' A.carrier)`.
    -- We can use our hypothesis that the closures are equal to switch from A to B.
    rw [h_closures_eq]

    -- The goal is now `↑x ∈ closure (↑ '' B.carrier)`.
    -- This is true because `x` is in `B`, so `↑x` is in the image of `B`,
    -- and any set is a subset of its closure.
    apply subset_closure
    exact mem_image_of_mem Subtype.val hx_in_B



-- We define the order on IrreducibleCloseds by using the subset relation on their carriers.
instance : PartialOrder (IrreducibleCloseds X) where
  le s t := s.carrier ⊆ t.carrier
  le_refl s := by
    -- The goal is s.carrier ⊆ s.carrier, which is true by definition.
    exact Set.Subset.refl _
  le_trans s t u hst htu := by
    -- We have hst : s.carrier ⊆ t.carrier and htu : t.carrier ⊆ u.carrier.
    -- The goal is s.carrier ⊆ u.carrier. This is just transitivity of subsets.
    exact Set.Subset.trans hst htu
  le_antisymm s t hst hts := by
    -- The goal is s = t. We prove this by proving their carriers are equal.
    apply IrreducibleCloseds.ext
    -- The goal is now s.carrier = t.carrier.
    -- This follows from antisymmetry of subsets, using our hypotheses.
    exact Set.Subset.antisymm hst hts

lemma IrreducibleCloseds.le_iff_subset {s t : IrreducibleCloseds X} :
    s ≤ t ↔ s.carrier ⊆ t.carrier := by
  -- This is true by the definition of `le` in our `PartialOrder` instance.
  rfl

lemma IrreducibleCloseds.lt_iff_subset {s t : IrreducibleCloseds X} :
    s < t ↔ s.carrier ⊂ t.carrier := by
  constructor
  · -- First, prove the forward direction: `s < t → s.carrier ⊂ t.carrier`
    intro h_lt
    -- By definition, `s < t` implies `s ≤ t` and `s ≠ t`.
    have h_le := le_of_lt h_lt
    have h_ne := ne_of_lt h_lt
    -- We need to prove `s.carrier ⊂ t.carrier`, which is `s.carrier ⊆ t.carrier ∧ s.carrier ≠ t.carrier`.
    rw [ssubset_iff_subset_ne]
    constructor
    · -- The subset part follows from `s ≤ t` and our `le_iff_subset` lemma.
      rw [← IrreducibleCloseds.le_iff_subset]
      exact h_le
    · -- The inequality part follows from `s ≠ t` and the extensionality principle.
      -- `s ≠ t` is equivalent to `s.carrier ≠ t.carrier`.
      apply mt IrreducibleCloseds.ext
      exact h_ne
  · -- Now, prove the backward direction: `s.carrier ⊂ t.carrier → s < t`
    intro h_ssubset
    -- We need to prove `s < t`, which is `s ≤ t ∧ s ≠ t`.
    rw [lt_iff_le_and_ne]
    -- Unpack the strict subset hypothesis into its two parts.
    rcases h_ssubset with ⟨h_subset, h_ne_carrier⟩
    constructor
    · -- The `s ≤ t` part follows from `s.carrier ⊆ t.carrier`.
      rw [IrreducibleCloseds.le_iff_subset]
      exact h_subset
    · -- The `s ≠ t` part follows from `s.carrier ≠ t.carrier`.
      intro h_s_eq_t
      -- If s = t, then s.carrier = t.carrier, which contradicts our hypothesis.
      apply h_ne_carrier
      rw [h_s_eq_t]

lemma map_irreducible_closed_strictMono (Y : Set X) :
    StrictMono (map_irreducible_closed Y) := by
  -- We want to prove that `A < B` implies `map A < map B`.
  intro A B h_less_AB

  -- The definition of `<` is `... ≤ ... ∧ ¬ (... ≤ ...)`
  constructor

  · -- Part 1: Prove `map A ≤ map B`.
    -- This means `(map A).carrier ⊆ (map B).carrier`.
    apply closure_mono
    apply image_subset
    -- This follows from `A ≤ B`, which is implied by `A < B`.
    exact le_of_lt h_less_AB

  · -- Part 2: Prove `¬(map B ≤ map A)`.
    -- We prove this by contradiction. Assume the opposite.
    intro h_contra_le
    -- `h_contra_le` is the hypothesis `map B ≤ map A`.

    -- From Part 1, we already know the map is monotone, so we also have the forward inclusion.
    have h_forward_subset : (map_irreducible_closed Y A).carrier ⊆ (map_irreducible_closed Y B).carrier := by
      apply closure_mono
      apply image_subset
      exact le_of_lt h_less_AB

    -- The hypothesis `h_contra_le` is `(map B).carrier ⊆ (map A).carrier`.
    -- By antisymmetry, these two inclusions imply the carriers are equal.
    have h_carrier_eq : (map_irreducible_closed Y A).carrier = (map_irreducible_closed Y B).carrier :=
      Subset.antisymm h_forward_subset h_contra_le

    -- We've already proven that if the images of the carriers are equal, then A and B are equal.
    have h_A_eq_B : A = B := by
      apply map_irreducible_closed_injective Y
      apply IrreducibleCloseds.ext
      exact h_carrier_eq

    -- This contradicts our main hypothesis `h_less_AB`, which states `A < B`.
    exact (ne_of_lt h_less_AB) h_A_eq_B


-- Part 1: Subspace dimension inequality
theorem top_KrullDim_subspace_le (X : Type*) [TopologicalSpace X] (Y : Set X) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  -- The topological Krull dimension is defined as the Krull dimension of the
  -- poset of irreducible closed subsets.
  unfold topologicalKrullDim
  -- The lemma `krullDim_le_of_strictMono` states that if there is a strictly
  -- monotone map `f : α → β` between two partial orders, then `krullDim α ≤ krullDim β`.
  -- We apply this to our map `map_irreducible_closed Y`.
  apply krullDim_le_of_strictMono (map_irreducible_closed Y)
  -- We have already proven that this map is strictly monotone.
  exact map_irreducible_closed_strictMono Y




theorem topological_dim_proper_closed_subset_lt (X : Type*) [TopologicalSpace X]
  (Y : Set X) (hX_irred : IsIrreducible (Set.univ : Set X))
  (hX_finite : topologicalKrullDim X ≠ ⊤)
  (hY_closed : IsClosed Y)
  (hY_proper : Y ⊂ Set.univ)
  (hY_nonempty : Y.Nonempty) :
  topologicalKrullDim Y < topologicalKrullDim X := by
  apply lt_of_le_of_ne (top_KrullDim_subspace_le X Y)
  intro h_dim_eq


  have h_dim_exists : ∃ n : ℕ∞, topologicalKrullDim X = ↑n := by
    -- We want to prove `∃ n, x = ↑n`.
    -- We will do this by proving `x ≠ ⊥` and then formally deriving the goal.

    -- Step 1: `apply Exists.imp (fun _ => Eq.symm)`
    -- This says: "I will prove `∃ n, x = ↑n` by first proving `∃ n, ↑n = x`."
    -- It uses symmetry of equality (`Eq.symm`) to bridge the two statements.
    -- The goal becomes `∃ n, ↑n = topologicalKrullDim X`.
    apply Exists.imp (fun _ => Eq.symm)

    -- Step 2: `apply (WithBot.ne_bot_iff_exists).mpr`
    -- This applies the `←` direction of the key `iff` lemma.
    -- The goal becomes `topologicalKrullDim X ≠ ⊥`.
    apply (WithBot.ne_bot_iff_exists).mp

    -- Step 3: Now we prove `... ≠ ⊥` as before.
    apply Order.krullDim_ne_bot_iff.mpr
    -- The goal is `⊢ Nonempty (IrreducibleCloseds X)`
    -- We will prove this by constructing an element.
    -- The `constructor` tactic changes the goal to `⊢ IrreducibleCloseds X`
    constructor

    -- To construct our element, we first need a point `x : X`.
    -- We need a point `x : X`. Since `hY_nonempty` is in `Prop`,
    -- we use `Nonempty.some` to extract a witness using classical logic.
    -- `hY_nonempty.some` has type `{x : X // x ∈ Y}`, so `.val` gives us the `x`.
    let x := hY_nonempty.some

    -- Now that we have a concrete `x : X`, we can use it to build our object.
    exact {
      carrier := closure {x},
      is_irreducible' := isIrreducible_singleton.closure,
      is_closed' := isClosed_closure
    }


  -- Now we can finally use h_dim_exists.
  obtain ⟨n, hn⟩ := h_dim_exists

  -- We know `n : ℕ∞`, but the best lemmas require a natural number `ℕ`.
  -- From `hX_finite` and `hn`, we know `n` is not `⊤`, so it must be finite.
  -- We use `WithTop.ne_top_iff_exists` to get the underlying `m : ℕ`.
  obtain ⟨m, hn_eq_m⟩ : ∃ m : ℕ, n = ↑m := by
    apply Exists.imp (fun _ => Eq.symm)
    apply WithTop.ne_top_iff_exists.mp
    intro hn_top
    rw [hn_top] at hn
    exact hX_finite hn

  -- Now we can state that `dim Y = m`.
  have h_dim_Y_eq_m : topologicalKrullDim ↑Y = ↑m := by
    rw [h_dim_eq, hn, hn_eq_m]
    -- The `↑` is ambiguous, so we specify the type.
    -- This says `↑(↑m : ℕ∞)` is the same as `↑m`.
    exact WithBot.coe_eq_coe.mpr (WithTop.coe_eq_coe.mpr rfl)

  -- From `dim Y = m`, we get `m ≤ dim Y`.
  -- Using `le_krullDim_iff`, this gives us a chain of length `m`.
  have h_chain_Y_exists := (le_krullDim_iff.mp (le_of_eq h_dim_Y_eq_m.symm))
  obtain ⟨c, hc_chain⟩ := h_chain_Y_exists

  let c' := List.map (map_irreducible_closed Y) c.toList
  -- We use `List.Chain'` (with a prime), as all elements of the chain are within the list `c'`.
  have hc'_chain : List.Chain' (· < ·) c' := by
    -- We use `List.Chain'.map_of_chain'`, which takes the function `f` as an argument.
    apply List.chain'_map_of_chain' (map_irreducible_closed Y)
    -- The first goal is to prove the function is strictly monotone.
    · exact map_irreducible_closed_strictMono Y
    -- The second goal is to prove the original list `c.toList` was a chain.
    · exact RelSeries.toList_chain' c

  -- Extend the chain in X by adding `univ` to get a longer chain.
  let X_ics : IrreducibleCloseds X := ⟨Set.univ, hX_irred, isClosed_univ⟩
  have h_last_lt_X : List.getLast c' (by
      -- This is the proof that `c'` is non-empty.
      apply List.ne_nil_of_length_pos
      -- First, unfold the definition of `c'` in the goal.
      dsimp only [c']
      -- We provide the specific rewrite lemmas instead of a general simp.
      rw [List.length_map, RelSeries.length_toList, hc_chain]
      linarith) < X_ics := by

    -- Part 1: Prove the helper lemma `h_last_eq`.
    let last_Y := c.last
    have h_last_eq : List.getLast c' (by
        -- This is the correct proof that `c'` is not empty.
        apply List.ne_nil_of_length_pos
        simp [c', RelSeries.length_toList, hc_chain, List.length_map]
      ) = map_irreducible_closed Y last_Y := by

      -- The main proof starts here.
      rw [List.getLast_map]
      congr
      -- The goal is `(RelSeries.toList c).getLast ... = last_Y`.
      -- First, unfold the `let` binding for `last_Y` to expose its definition.
      dsimp [last_Y]
      -- The goal becomes `(RelSeries.toList c).getLast ... = c.last`.

      -- Now, rewrite `getLast` using its fundamental definition in terms of `getElem`.
      rw [List.getLast_eq_getElem]

      simp only [RelSeries.length_toList, hc_chain]
      simp only [Nat.add_one_sub_one] -- changes `m - 1` to `m + 1 - 1`

      -- The goal is now `(RelSeries.toList c)[m] = RelSeries.last c`.

      -- Step 2: Unfold the `getElem` notation using the `change` tactic.
      change (RelSeries.toList c).get ⟨m, ?_⟩ = RelSeries.last c

      -- The goal is now `(RelSeries.toList c).get ⟨m, _⟩ = RelSeries.last c`.
      -- We simplify both sides, but the result is messy.
      simp only [RelSeries.toList, List.get_ofFn, RelSeries.last]

      -- The goal is now `c.toFun (Fin.cast ...) = c.toFun (Fin.last c.length)`.
      -- Step 3: Use `congr` to prove the arguments are equal.
      congr

      -- The goal is now `Fin.cast ... = Fin.last c.length`.
      -- We can prove two `Fin`s are equal by proving their numerical values are equal.
      apply Fin.eq_of_val_eq

      -- The goal is now `(Fin.cast ...).val = (Fin.last c.length).val`.
      -- This is an equality of natural numbers, which `simp` can solve easily.
      simp [hc_chain]



    -- Part 2: Use the helper lemma and finish the proof.
    rw [h_last_eq, IrreducibleCloseds.lt_iff_subset]

    -- Use `change` to unfold the definition of the carrier in the goal. This is robust.
    change (closure (Subtype.val '' c.last.carrier)) ⊂ X_ics.carrier

    have h_carrier_closed_in_X : IsClosed (Subtype.val '' c.last.carrier) :=
      IsClosed.isClosedMap_subtype_val hY_closed _ c.last.is_closed'
    rw [h_carrier_closed_in_X.closure_eq]

    have h_subset_Y : Subtype.val '' c.last.carrier ⊆ Y := by
      rintro _ ⟨y, _, rfl⟩; exact y.property
    exact ssubset_of_subset_of_ssubset h_subset_Y hY_proper -- I'll fill this in later

  let extended_chain := c' ++ [X_ics]
  have h_extended_chain : List.Chain' (· < ·) extended_chain := by
    apply List.Chain'.append
    · exact hc'_chain
    · simp -- proves `[X_ics]` is a chain
    · -- The goal is `∀ x ∈ c'.getLast?, ∀ y ∈ [X_ics].head?, x < y`.
      -- We introduce the variables and hypotheses from the goal.
      intro last_val h_last_mem first_val h_first_mem

      -- We know `c'` is non-empty, so `getLast?` will be `some ...`.
      have h_c'_ne_nil : c' ≠ [] := by
        apply List.ne_nil_of_length_pos
        simp only [c', List.length_map, RelSeries.length_toList, hc_chain]
        linarith

      -- Now we simplify our hypotheses `h_last_mem` and `h_first_mem`
      -- to get equalities.
      rw [List.getLast?_eq_getLast h_c'_ne_nil, Option.mem_some_iff] at h_last_mem
      rw [List.head?_cons, Option.mem_some_iff] at h_first_mem

      -- Now we have:
      -- `h_last_mem : last_val = c'.getLast ...`
      -- `h_first_mem : first_val = X_ics`
      -- We rewrite the goal `last_val < first_val` using these equalities.
      rw [← h_last_mem, ← h_first_mem]

      -- The goal is now `c'.getLast ... < X_ics`, which is exactly `h_last_lt_X`.
      exact h_last_lt_X

  -- Derive the contradiction.
  have h_new_chain_len : extended_chain.length = m + 2 := by
    -- We provide simp with all the lemmas needed to compute the length.
    simp [extended_chain, c', List.length_append, List.length_singleton, List.length_map, RelSeries.length_toList, hc_chain]

  have h_dim_ge_m_plus_1 : ↑(m + 1) ≤ topologicalKrullDim X := by
    -- To prove this, we must provide a chain of length `m + 1`.
    unfold topologicalKrullDim
    rw [le_krullDim_iff]

    -- Step 1: Prove that our list `extended_chain` is not empty.
    have h_extended_chain_ne_nil : extended_chain ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [h_new_chain_len]
      linarith

    -- Step 2: Use this non-empty list to construct the required `LTSeries`.
    -- We provide `h_extended_chain_ne_nil` as the argument it needs.
    use RelSeries.fromListChain' extended_chain h_extended_chain_ne_nil h_extended_chain

    -- Step 3: Prove that the length of this series is `m + 1`.
    -- The length of a series from a list is `list.length - 1`.
    simp [h_new_chain_len]

  -- This contradicts `dim X = m`.
  rw [← h_dim_eq, h_dim_Y_eq_m] at h_dim_ge_m_plus_1
  norm_cast at h_dim_ge_m_plus_1

  linarith



-- Part 2: Dimension via open covering
-- Helper lemma: if X is empty, then IrreducibleCloseds X is empty

lemma IrreducibleCloseds.isEmpty_of_isEmpty {X : Type*} [TopologicalSpace X]
    (h : IsEmpty X) : IsEmpty (IrreducibleCloseds X) := by
  constructor
  intro ic
  -- Derive contradiction: irreducible sets are nonempty but X is empty
  have h_nonempty : ic.carrier.Nonempty := IsIrreducible.nonempty ic.is_irreducible'
  have h_empty_carrier : ic.carrier = ∅ := by
    -- ic.carrier is a subset of X, and when X is empty, any subset is empty
    apply Set.eq_empty_of_forall_notMem
    intro x hx
    -- x ∈ ic.carrier, but X is empty so no such x exists
    exact IsEmpty.elim h x
  rw [h_empty_carrier] at h_nonempty
  exact Set.not_nonempty_empty h_nonempty

-- Helper lemma with the corrected premise.
lemma nonempty_inter_of_chain {X : Type*} [TopologicalSpace X]
    (c : LTSeries (IrreducibleCloseds X)) (U : Set X)
    -- We now assume the intersection with the smallest set is non-empty.
    (h_int_zero : ((c.toFun 0).carrier ∩ U).Nonempty) (i : Fin (c.length + 1)) :
    ((c.toFun i).carrier ∩ U).Nonempty := by
  -- The first set Z₀ is a subset of every other set Zᵢ in the increasing chain.
  have h_subset : (c.toFun 0).carrier ⊆ (c.toFun i).carrier := by
    have h_mono : Monotone c.toFun := (Fin.strictMono_iff_lt_succ.mpr c.step).monotone
    exact h_mono (Fin.zero_le i)
  -- If U intersects the smaller set Z₀, it must also intersect the larger set Zᵢ.
  apply Set.Nonempty.mono _ h_int_zero
  exact inter_subset_inter h_subset fun ⦃a⦄ a ↦ a


lemma chain_restriction_to_open_cover {X : Type*} [TopologicalSpace X]
    (c : LTSeries (IrreducibleCloseds X)) (U : Set X) (hU : IsOpen U)
    (h_int : ((c.toFun 0).carrier ∩ U).Nonempty) :
    ∃ d : LTSeries (IrreducibleCloseds ↑U), d.length = c.length := by

  -- Step 1: Define the function that creates the new chain `d`.
  -- For each index `i`, `d_fun i` is the set `Zᵢ ∩ U` viewed as an object in `IrreducibleCloseds U`.
  let d_fun (i : Fin (c.length + 1)) : IrreducibleCloseds U := {
    carrier := Subtype.val ⁻¹' (c.toFun i).carrier,

    is_irreducible' := by
      -- We split the goal into proving `Nonempty` and `IsPreirreducible`.
      constructor

      · -- Goal 1: Prove the set is nonempty.
        -- This is equivalent to `(Zᵢ ∩ U).Nonempty`, which our helper lemma does.
        rw [Subtype.preimage_coe_nonempty]
        rw [Set.inter_comm U]
        --rw [← Set.nonempty_coe_sort, ← Subtype.preimage_coe_self_inter]
        exact nonempty_inter_of_chain c U h_int i

      · -- Goal 2: Prove the set is preirreducible.
        -- We use your suggested lemma, `IsPreirreducible.preimage`.
        apply IsPreirreducible.preimage
        · -- First, we provide the proof that the original set `Zᵢ` is preirreducible.
          exact (c.toFun i).is_irreducible'.isPreirreducible
        · -- Second, we must prove that the function `Subtype.val : U → X` is an open embedding.
          -- This is a standard lemma in Mathlib.
          exact IsOpen.isOpenEmbedding_subtypeVal hU

    is_closed' := by
      -- The preimage of a closed set under a continuous map is closed.
      exact (c.toFun i).is_closed'.preimage continuous_subtype_val
  }

  -- Step 2: Prove that our new sequence `d_fun` is strictly increasing.
  have h_strict_mono : StrictMono d_fun := by
    intro i j h_lt_ij
    -- Unfold definitions to the goal: `Zᵢ ∩ U ⊂ Zⱼ ∩ U`
    simp_rw [IrreducibleCloseds.lt_iff_subset, d_fun]
     -- This will expose the carrier definition.

    let Zᵢ := (c.toFun i).carrier
    let Zⱼ := (c.toFun j).carrier

    -- 1. The `c.step` field proves the chain is strictly increasing for adjacent elements.
    -- 2. We use `Fin.strictMono_iff_lt_succ` to build the full `StrictMono` property from `c.step`.
    have h_c_mono : StrictMono c.toFun := Fin.strictMono_iff_lt_succ.mpr c.step
    -- 3. Now we can apply this to our hypothesis `h_lt_ij` to prove `Zᵢ < Zⱼ`.
    have h_lt_Z : c.toFun i < c.toFun j := h_c_mono h_lt_ij
    -- 4. Finally, we convert this to the strict subset relation we need.
    have h_Z_ssubset : Zᵢ ⊂ Zⱼ := IrreducibleCloseds.lt_iff_subset.mp h_lt_Z

    -- A strict subset (`⊂`) means `⊆` and `≠`.
    rw [ssubset_iff_subset_ne]
    constructor
    · -- The `⊆` part is straightforward.
      rw [Subtype.preimage_val_subset_preimage_val_iff]
      refine inter_subset_inter_right U ?_
      exact subset_of_ssubset (h_c_mono h_lt_ij)
    · -- The `≠` part requires irreducibility. We prove it by contradiction.
      intro h_inter_eq
      -- `Zⱼ` is irreducible. We find two non-empty open subsets of `Zⱼ`
      -- whose intersection must therefore be non-empty.
      -- The open sets in X are `U` and `X \ Zᵢ`.
      have h_nonempty_inter_U : (Zⱼ ∩ U).Nonempty :=
        nonempty_inter_of_chain c U h_int j

      -- We want to show Zⱼ \ Zᵢ is non-empty.
      -- First, note that `Zⱼ ∩ Zᵢᶜ` is the definition of `Zⱼ \ Zᵢ`.
      have h_nonempty_inter_compl_Zᵢ : (Zⱼ \ Zᵢ).Nonempty := by
        -- The lemma `nonempty_diff_of_ssubset` directly proves this
        -- from our hypothesis that Zᵢ is a strict subset of Zⱼ.
        exact nonempty_of_ssubset h_Z_ssubset

      have h_triple_inter_nonempty : (Zⱼ ∩ (compl Zᵢ ∩ U)).Nonempty :=
        -- We call the proof of preirreducibility as a function with our prepared arguments.
        (c.toFun j).is_irreducible'.isPreirreducible (compl Zᵢ) U
          (isOpen_compl_iff.mpr (c.toFun i).is_closed') hU
          h_nonempty_inter_compl_Zᵢ h_nonempty_inter_U

      -- But our assumption `h_inter_eq` implies this intersection is empty.
      have h_inter_empty : (Zⱼ \ Zᵢ) ∩ U = ∅ := by
        -- First, let's rewrite the set difference `Zⱼ \ Zᵢ` to make the intersection clearer.
        rw [Set.diff_eq_compl_inter]
        -- Goal: `(Zⱼ ∩ Zᵢᶜ) ∩ U = ∅`
        -- Now, let's rearrange the intersections to group `Zⱼ ∩ U` together.
        rw [Set.inter_assoc, Set.inter_comm]
        -- Goal: `(Zⱼ ∩ U) ∩ Zᵢᶜ = ∅`
        -- Our hypothesis `h_inter_eq` is `Subtype.val ⁻¹' Zᵢ = Subtype.val ⁻¹' Zⱼ`.
        -- We translate this to `Zᵢ ∩ U = Zⱼ ∩ U` to use it in our goal.
        rw [Subtype.preimage_coe_eq_preimage_coe_iff, Set.inter_comm U _, Set.inter_comm U _] at h_inter_eq
        -- Now, we can replace `Zⱼ ∩ U` with `Zᵢ ∩ U` using our translated hypothesis.
        change Zᵢ ∩ U = Zⱼ ∩ U at h_inter_eq

        rw [← h_inter_eq]
        -- Goal: `(Zᵢ ∩ U) ∩ Zᵢᶜ = ∅`
        -- This is true because `Zᵢ ∩ Zᵢᶜ` is the empty set.

        rw [Set.inter_assoc, Set.inter_comm, Set.inter_assoc]
        simp only [compl_inter_self, inter_empty, d_fun]




      -- The final contradiction:
      -- We have `h_triple_inter_nonempty` which says a set is non-empty.
      -- We have `h_inter_empty` which says the same set is empty.

      -- First, we use `h_inter_empty` to rewrite our non-emptiness proof.
      -- We have to use associativity (`Set.inter_assoc`) to match the parentheses.
      simp only [Set.inter_assoc, Set.diff_eq_compl_inter] at h_inter_empty
      rw [inter_left_comm] at h_inter_empty
      exact h_triple_inter_nonempty.ne_empty h_inter_empty



-- Step 3: Assemble the `LTSeries` and prove the length is correct.
  use {
    length := c.length,
    toFun := d_fun,
    step := by
      -- We need to prove `d_fun i < d_fun (i.succ)` for any `i`.
      intro i
      -- Our main hypothesis `h_strict_mono` proves that if `a < b`, then `d_fun a < d_fun b`.
      -- Let's apply it to the goal.
      apply h_strict_mono
      -- The new goal is to prove that `i` (as `i.castSucc`) is indeed less than `i.succ`.
      -- This is a standard property of `Fin` types, proven by the lemma `Fin.lt_succ`.
      simp only [Fin.castSucc_lt_succ_iff, le_refl, d_fun]
  }




theorem topological_dim_open_cover (X : Type*) [TopologicalSpace X]
  (ι : Type*) (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ) :
  topologicalKrullDim X = ⨆ i, topologicalKrullDim (U i) := by

  -- Handle the empty space case first
  by_cases h_empty : IsEmpty X
  · -- Case: X is empty
    -- First show that each U i is also empty
    have h_U_empty : ∀ i, IsEmpty (U i) := by
      intro i
      -- We prove U i is empty by showing U i ⊆ X and X is empty
      have hU_subset_X : U i ⊆ (Set.univ : Set X) := by
        exact Set.subset_univ _
      have h_univ_empty : (Set.univ : Set X) = ∅ := by
        apply Set.eq_empty_of_isEmpty
      rw [h_univ_empty, Set.subset_empty_iff] at hU_subset_X

      apply Set.isEmpty_coe_sort.mpr
      exact hU_subset_X


    -- Both sides are equal when everything is empty
    have h_X_empty_krull : topologicalKrullDim X = ⊥ := by
      unfold topologicalKrullDim
      have ic_X_empty : IsEmpty (IrreducibleCloseds X) := IrreducibleCloseds.isEmpty_of_isEmpty h_empty
      rw [krullDim_eq_bot]

    have h_U_empty_krull : ⨆ i, topologicalKrullDim ↑(U i) = ⊥ := by
      unfold topologicalKrullDim
      have ic_U_empty : ∀ i, IsEmpty (IrreducibleCloseds ↑(U i)) := by
        intro i
        apply IrreducibleCloseds.isEmpty_of_isEmpty
        exact h_U_empty i
      rw [iSup_eq_bot]
      intro i
      rw [krullDim_eq_bot]
    rw [h_X_empty_krull, h_U_empty_krull]

  -- Case: X is nonempty
  · -- Now we have [Nonempty X] available
    rw [not_isEmpty_iff] at h_empty

    -- Key insight: Use the characterization via supremum of chain lengths
    unfold topologicalKrullDim

    -- Both sides are supremums over chain lengths, so we show they're equal
    -- by showing each chain on one side corresponds to a chain on the other side

    -- We need nonemptiness for the characterization lemmas
    have h_irreducible_nonempty : Nonempty (IrreducibleCloseds X) := by
          constructor
        -- We can construct an irreducible closed set: the closure of any singleton
          let x := h_empty.some-- this : Nonempty X
          exact {
            carrier := closure {x},
            is_irreducible' := isIrreducible_singleton.closure,
            is_closed' := isClosed_closure
          }


    -- Since U covers X and X is nonempty, at least one U i is nonempty
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

    -- Now use the key characterization lemmas
    -- simp only [krullDim_eq_iSup_length]


    apply le_antisymm

    · -- First direction: dim X ≤ supᵢ dim Uᵢ
      -- "For any `b` that is an upper bound of all `dim(Uᵢ)`, prove `dim(X) ≤ b`."
      rw [le_iSup_iff]

      -- Let `b` be an arbitrary upper bound for the dimensions of the `Uᵢ`.
      intro b h_b_is_upper_bound

      -- To prove `krullDim X ≤ b`, we will show that the length of any chain in `X`
      -- is less than or equal to `b`. The Krull dimension is the supremum of these lengths.
      apply iSup_le

      -- Let `c` be an arbitrary chain `Z₀ ⊃ Z₁ ⊃ ... ⊃ Zₗ` in `X`.
      intro c

      -- "Then there exists Uᵢ such that Uᵢ ∩ Zₗ ≠ ∅."
      -- We find an `i₀` such that `U i₀` intersects the smallest set in the chain, `c.last`.
      -- We must find an open set Uᵢ that intersects the SMALLEST set in the increasing chain, which is `c.toFun 0`.
      have h_first_intersects : ∃ i, ((c.toFun 0).carrier ∩ U i).Nonempty := by
        -- The smallest set Z₀ is non-empty because it's irreducible.
        have h_nonempty : (c.toFun 0).carrier.Nonempty := (c.toFun 0).is_irreducible'.nonempty
        -- Since the U's cover all of X, they must also cover the subset Z₀.
        have h_subset : (c.toFun 0).carrier ⊆ ⋃ i, U i := by
          rw [hcover]
          exact Set.subset_univ _
        -- A non-empty set covered by a union of sets must have a non-empty intersection with at least one of them.
        obtain ⟨x, hx_in_first⟩ := h_nonempty
        have hx_in_union : x ∈ ⋃ i, U i := h_subset hx_in_first
        obtain ⟨i₀, hx_in_Ui₀⟩ := Set.mem_iUnion.mp hx_in_union
        exact ⟨i₀, ⟨x, hx_in_first, hx_in_Ui₀⟩⟩

      -- Now we have the required index `i₀` and the proof of non-empty intersection `h_int`.
      obtain ⟨i₀, h_int⟩ := h_first_intersects

      -- "Moreover the closure of Uᵢ ∩ Zⱼ in X is Zⱼ and thus the Zⱼ ∩ Uᵢ form
      -- a chain of length l in Uᵢ."
      -- This is the key step, which requires your helper lemma. We obtain a chain `d`
      -- in `U i₀` that has the same length as `c`.
      obtain ⟨d, hd_len⟩ : ∃ d : LTSeries (IrreducibleCloseds ↑(U i₀)), d.length = c.length := by
        exact chain_restriction_to_open_cover c (U i₀) (hU i₀) h_int

      -- Now we can conclude with a simple chain of inequalities.
      -- The length `l` of chain `c` is equal to the length of chain `d`.
      -- The length of `d` is ≤ dim(U i₀).
      -- And dim(U i₀) is ≤ `b` by our hypothesis.
      calc (c.length : WithBot ℕ∞)
          = (d.length : WithBot ℕ∞)      := by rw [hd_len]
        _ ≤ topologicalKrullDim ↑(U i₀) := LTSeries.length_le_krullDim d
        _ ≤ b                           := h_b_is_upper_bound i₀

    · -- Show ⨆ i, krullDim (U i) ≤ krullDim X
      apply iSup_le
      intro i
      exact top_KrullDim_subspace_le X (U i)

-- Part 3: Dimension via irreducible components

-- A helper lemma to show that a maximal preirreducible set is an irreducible component.
lemma maximal_preirreducible_is_irred_component {t : Set X} (h_nonempty : t.Nonempty)
    (h_preirred : IsPreirreducible t)
    (h_maximal : ∀ u, IsPreirreducible u → t ⊆ u → u = t) :
    t ∈ irreducibleComponents X := by
  -- An irreducible component is a maximal irreducible set.
  -- 1. Show `t` is irreducible.
  have h_irred : IsIrreducible t := ⟨h_nonempty, h_preirred⟩
  -- 2. Show `t` is maximal among irreducible sets.
  refine ⟨h_irred, ?_⟩
  intro u h_u_irred h_t_subset_u
  -- Since `u` is irreducible, it's also preirreducible.
  -- By the maximality property of `t`, we are done.
  simp only [le_eq_subset]
  simp only [le_eq_subset] at h_t_subset_u

  have h_u_t : u=t := h_maximal u h_u_irred.isPreirreducible h_t_subset_u
  rw [h_u_t]


-- The main theorem with the simplified signature.
theorem topological_dim_irreducible_components (X : Type*) [TopologicalSpace X] :
    topologicalKrullDim X = ⨆ (Y ∈ irreducibleComponents X), topologicalKrullDim Y := by
  unfold topologicalKrullDim
  apply le_antisymm

  · -- Direction 1: `dim X ≤ sup_{Y ∈ Components} dim Y`
    -- To prove this, we show that the length of any chain in X is bounded by the RHS.
    apply iSup_le
    intro c -- `c` is an arbitrary chain Z₀ ⊂ ... ⊂ Zₙ of irreducible closed sets in X.

    -- Let Z_last be the largest set in the chain. It's irreducible.
    let Z_last := c.last
    have h_Z_last_irred : IsIrreducible Z_last.carrier := Z_last.is_irreducible'

    -- By `exists_preirreducible`, Z_last is contained in a maximal preirreducible set.
    obtain ⟨Y_comp, h_Y_preirred, h_Z_subset_Y, h_Y_maximal⟩ :=
      exists_preirreducible Z_last.carrier h_Z_last_irred.isPreirreducible

    -- This maximal set `Y_comp` is, by definition, an irreducible component.
    have hY_comp_in_components : Y_comp ∈ irreducibleComponents X := by
      have h_nonempty : Y_comp.Nonempty := Nonempty.mono h_Z_subset_Y h_Z_last_irred.nonempty
      exact maximal_preirreducible_is_irred_component h_nonempty h_Y_preirred h_Y_maximal

    -- The entire chain `c` is contained in this component `Y_comp`.
    have h_chain_in_Y : ∀ i, (c.toFun i).carrier ⊆ Y_comp := by
      intro i
      have h_mono : Monotone c.toFun := (Fin.strictMono_iff_lt_succ.mpr c.step).monotone
      exact Subset.trans (h_mono (Fin.le_last i)) h_Z_subset_Y

    -- Therefore, the length of `c` is at most the dimension of `Y_comp`.
    have h_len_le_dim_Y : (c.length : WithBot ℕ∞) ≤ krullDim (IrreducibleCloseds ↑Y_comp) := by
      -- This step requires constructing the chain `c` as a chain in the subspace `Y_comp`.
      let d_fun (i : Fin (c.length + 1)) : IrreducibleCloseds Y_comp := {
        carrier := {y : Y_comp | y.val ∈ (c.toFun i).carrier},
        is_irreducible' := by
          constructor
          · -- Prove nonemptiness
            have h_nonempty : (c.toFun i).carrier.Nonempty := (c.toFun i).is_irreducible'.nonempty
            obtain ⟨x, hx_in_Zi⟩ := h_nonempty
            have hx_in_Y : x ∈ Y_comp := h_chain_in_Y i hx_in_Zi
            exact ⟨⟨x, hx_in_Y⟩, hx_in_Zi⟩
          · -- Goal 2: Prove the carrier is preirreducible.
            -- This follows from the fact that `Z_i` is preirreducible in `X`,
            -- and the subspace topology on `Z_i` inherited from `Y_comp` is the
            -- same as the one inherited from `X`.
            intro u v hu hv h_nonempty_u h_nonempty_v
            -- Let `Z_i` be the carrier of the i-th set in the original chain.
            let Z_i := (c.toFun i).carrier
            -- The carrier of our new set `d i` is the preimage of `Z_i` in `Y_comp`.
            let d_carrier := {y : Y_comp | y.val ∈ Z_i}

            -- `u` and `v` are open in `Y_comp`. The subspace topology means they are
            -- intersections of `Y_comp` with open sets from `X`.
            obtain ⟨U, hU_open, rfl⟩ := isOpen_induced_iff.mp hu
            obtain ⟨V, hV_open, rfl⟩ := isOpen_induced_iff.mp hv

            -- We need to translate our non-emptiness hypotheses from `Y_comp` back to `X`.
            -- `d_carrier ∩ (Y_comp ∩ U)` is just `d_carrier ∩ U` (in X).
            -- And since `d_carrier` are just the points of `Z_i`, this is `Z_i ∩ U`.
            have h_nonempty_U_in_X : (Z_i ∩ U).Nonempty := by
              exact nonempty_of_nonempty_preimage h_nonempty_u

            have h_nonempty_V_in_X : (Z_i ∩ V).Nonempty := by
              exact nonempty_of_nonempty_preimage h_nonempty_v


            -- Now we can use the fact that `Z_i` is preirreducible in `X`.
            have h_inter_nonempty_in_X :=
              (c.toFun i).is_irreducible'.isPreirreducible U V hU_open hV_open
                h_nonempty_U_in_X h_nonempty_V_in_X

            -- The hypothesis `h_inter_nonempty_in_X` tells us the intersection in the ambient
            -- space `X` is nonempty. Let's get a point `x` from that intersection.
            obtain ⟨x, hx_in_inter⟩ := h_inter_nonempty_in_X
            have hx_in_Z_i : x ∈ Z_i := hx_in_inter.1
            have hx_in_U_and_V : x ∈ U ∩ V := hx_in_inter.2

            -- We know `Z_i` is contained in `Y_comp`, so our point `x` is also in `Y_comp`.
            have hx_in_Y_comp : x ∈ Y_comp := (h_chain_in_Y i) hx_in_Z_i

            -- Now we can construct the point `y` in the subspace `Y_comp`. This is our witness.
            let y : Y_comp := ⟨x, hx_in_Y_comp⟩

            -- We use `y` to prove the goal `(d_carrier ∩ (u ∩ v)).Nonempty`.
            use y

            -- The goal now is to prove `y` is in the set `d_carrier ∩ (u ∩ v)`.
            -- This splits into proving `y ∈ d_carrier` and `y ∈ u ∩ v`.
            constructor
            · -- Goal `y ∈ d_carrier` means `↑y ∈ Z_i`. By definition, `↑y` is `x`.
              exact hx_in_Z_i
            · -- Goal `y ∈ u ∩ v` splits into `y ∈ u` and `y ∈ v`.
              constructor
              · -- Goal `y ∈ u` means `↑y ∈ U`.
                exact hx_in_U_and_V.1
              · -- Goal `y ∈ v` means `↑y ∈ V`.
                exact hx_in_U_and_V.2



        is_closed' := (c.toFun i).is_closed'.preimage continuous_subtype_val
      }

      have h_d_strict_mono : StrictMono d_fun := by
        intro i j h_lt
        -- We want to prove `d_fun i < d_fun j`. By definition, this means
        -- the carrier of `d i` is a strict subset of the carrier of `d j`.
        rw [IrreducibleCloseds.lt_iff_subset, ssubset_iff_subset_ne]

        -- We prove the two parts (subset and inequality) separately.
        constructor

        · -- Part 1: Prove `(d_fun i).carrier ⊆ (d_fun j).carrier`.
          -- Unfold the definition of the carrier.
          change (Subtype.val ⁻¹' (c.toFun i).carrier) ⊆ (Subtype.val ⁻¹' (c.toFun j).carrier)

          -- The original chain `c` is strictly monotone, so `c i < c j`.
          have h_c_lt := (Fin.strictMono_iff_lt_succ.mpr c.step) h_lt
          -- This implies the carriers are subsets: `(c i).carrier ⊆ (c j).carrier`.
          have h_c_subset : (c.toFun i).carrier ⊆ (c.toFun j).carrier := le_of_lt h_c_lt

          -- The `preimage` operation preserves subset relations (it's monotone).
          exact Set.preimage_mono h_c_subset

        · -- Part 2: Prove `(d_fun i).carrier ≠ (d_fun j).carrier`.
          -- We prove this by contradiction.
          intro h_eq

          -- `h_eq` is the hypothesis `(preimage val (c i).carrier) = (preimage val (c j).carrier)`.
          -- The function `Subtype.val : Y_comp → X` is injective. Because our sets `Z_i` and `Z_j`
          -- are both contained in its range (`Y_comp`), the equality of their preimages
          -- implies the equality of the sets themselves.
          have h_carriers_eq : (c.toFun i).carrier = (c.toFun j).carrier := by
            -- We start with the hypothesis `h_eq : (preimage val Z_i) = (preimage val Z_j)`
            -- We apply the forward direction of `preimage_eq_preimage'` to `h_eq`.
            apply (preimage_eq_preimage' _ _).mp h_eq
            · -- The first condition: `(c i).carrier ⊆ range val`
              -- The range of `val` is `Y_comp`.
              rw [Subtype.range_val]
              exact h_chain_in_Y i

            · -- The second condition: `(c j).carrier ⊆ range val`
              rw [Subtype.range_val]
              exact h_chain_in_Y j

          -- This equality contradicts the fact that the original chain `c` is strictly increasing.
          have h_c_lt := (Fin.strictMono_iff_lt_succ.mpr c.step) h_lt
          have h_c_ne := ne_of_lt h_c_lt

          -- `h_c_ne` says `c i ≠ c j`. By extensionality, this means their carriers are not equal.
          apply h_c_ne
          exact IrreducibleCloseds.ext h_carriers_eq



      -- This is the block you need to insert to finish the proof of `h_len_le_dim_Y`.

      -- 1. Formally define the new chain `d` in the subspace Y_comp.
      let d : LTSeries (IrreducibleCloseds Y_comp) := {
        toFun := d_fun,
        step := fun i => h_d_strict_mono (by simp : Fin.castSucc i < Fin.succ i),
        length := c.length
      }

      -- 2. The `convert` tactic applies the lemma `LTSeries.length_le_krullDim d`
      --    (which proves `↑d.length ≤ ...`) and changes our goal to proving that
      --    `c.length` is equal to `d.length`.
      convert LTSeries.length_le_krullDim d


    -- Finally, dim(Y_comp) is bounded by the supremum over all components.

    -- We have `h_len_le_dim_Y : (c.length : WithBot ℕ∞) ≤ krullDim (IrreducibleCloseds ↑Y_comp)`
    -- Now we prove that the dimension of this one component is less than the supremum of all of them.
    have h_dim_le_sup : krullDim (IrreducibleCloseds ↑Y_comp) ≤ ⨆ (Y ∈ irreducibleComponents X), krullDim (IrreducibleCloseds ↑Y) := by
      -- Let's define our function `f` and our set of components `S` for clarity.
      let f := fun (Y : Set X) => krullDim (IrreducibleCloseds ↑Y)
      let S := irreducibleComponents X

      rw [← sSup_image]
      -- The notation `⨆ Y ∈ S, f Y` is defined as the supremum of the image of S, `sSup (f '' S)`.
      -- We use `change` to make the goal explicit in these terms.
      change f Y_comp ≤ sSup (f '' S)

      -- The correct lemma for this is `le_csSup`, which requires two conditions:
      -- 1. The set `f '' S` must be bounded above.
      -- 2. Our element `f Y_comp` must be a member of `f '' S`.

      -- Proof of Condition 1: The set of component dimensions is bounded above by the dimension of X.
      have h_bdd_above : BddAbove (f '' S) := by
        use krullDim (IrreducibleCloseds X)  -- The proposed upper bound.
        rintro _ ⟨Y, hY_mem, rfl⟩          -- For any dimension `f Y` in the set...
        exact top_KrullDim_subspace_le X Y     -- ...prove `f Y ≤ dim(X)`.

      -- Proof of Condition 2: Our specific dimension `f Y_comp` is in the set.
      have h_mem : f Y_comp ∈ f '' S :=
        mem_image_of_mem f hY_comp_in_components

      -- Now we can finally apply the correct lemma with our proven conditions.

      exact le_csSup h_bdd_above h_mem


    -- Finally, combine our two inequalities.
    exact le_trans h_len_le_dim_Y h_dim_le_sup



        --le_iSup₂ Y_comp hY_comp_in_components

  · -- Direction 2: `sup_{Y ∈ Components} dim Y ≤ dim X`
    -- This is the easy direction. The dimension of any subspace is at most the dimension of the whole space.
    apply iSup₂_le
    intro Y hY
    exact top_KrullDim_subspace_le X Y




-- Definition: The dimension of a scheme is the Krull dimension of its underlying topological space
noncomputable def schemeDim (X : Scheme) : WithBot ℕ∞ :=
  topologicalKrullDim X.carrier

-- Part 4: For schemes, dimension equals supremum of local ring dimensions


-- We assume all the definitions and theorems from your files are available.

-- The main theorem, now correctly implemented.
theorem scheme_dim_eq_sup_local_rings (X : Scheme) :
    schemeDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x) := by
  let 𝒰 := X.affineCover
  unfold schemeDim
  rw [topological_dim_open_cover X.carrier 𝒰.J
      (fun i ↦ Set.range (𝒰.map i).base)
      (fun i ↦ IsOpenImmersion.isOpen_range (𝒰.map i))
      𝒰.iUnion_range]

  -- Rewrite the RHS as a supremum over the same affine open cover.
  have h_rhs_sup : (⨆ x : X, ringKrullDim (X.presheaf.stalk x)) =
      ⨆ (i : 𝒰.J), ⨆ (x : Set.range (𝒰.map i).base), ringKrullDim (X.presheaf.stalk x) := by
    -- We rewrite the domain `X` as the union of the cover's ranges, using `𝒰.iUnion_range`.

    rw [← iSup_univ, ← 𝒰.iUnion_range, iSup_iUnion]


    -- Finally, adjust for the stalk isomorphism between the scheme and the subscheme.
    apply iSup_congr
    intro i
    let U_opens : Opens X.carrier := (𝒰.map i).opensRange
    rw [iSup_subtype']


  rw [h_rhs_sup]

  apply iSup_congr
  intro i
  -- Let `f` be the i-th map in the cover, which is an open immersion.
  let f := 𝒰.map i
  haveI : IsOpenImmersion f := 𝒰.map_prop i
  let Y := 𝒰.obj i

  -- An open immersion induces a homeomorphism between the source and the range.
  let e_scheme : Y ≅ (f.opensRange : Scheme) := Scheme.Hom.isoOpensRange f

  -- Now, we convert the Scheme isomorphism into a homeomorphism of the underlying spaces.
  let e_homeo : Y.carrier ≃ₜ ↑(f.opensRange) :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e_scheme)

  -- Since the spaces are homeomorphic, their topological Krull dimensions are equal.
  -- Step 1: State the equality of dimensions as a fact, then rewrite the LHS of the goal.
  have dim_eq : topologicalKrullDim (Set.range f.base) = topologicalKrullDim Y.carrier :=
    (IsHomeomorph.topologicalKrullDim_eq e_homeo e_homeo.isHomeomorph).symm
  rw [dim_eq]

  -- Step 2: Explicitly prove the equality for the RHS and then rewrite.
  have rhs_eq : (⨆ x : ↥(Set.range f.base), ringKrullDim (X.presheaf.stalk x.val)) =
      (⨆ y : Y.carrier, ringKrullDim (X.presheaf.stalk (e_homeo y).val)) := by
    -- `rw` can use the lemma because it can infer the function from the goal.
    -- We rewrite the RHS of this equality using the lemma.
    rw [← Scheme.Hom.coe_opensRange]

    apply le_antisymm

    · -- First goal: `(⨆ x, ...) ≤ (⨆ y, ...)`
      apply iSup_le
      intro x
      -- We use `convert` to handle the substitution of `x` with `e_homeo (e_homeo.symm x)`.
      convert le_iSup (fun y' => ringKrullDim (X.presheaf.stalk (e_homeo y').val)) (e_homeo.symm x)
      -- The remaining goal is to prove the arguments are equal, which is true by definition.
      rw [Homeomorph.apply_symm_apply]
    · -- Second goal: `(⨆ y, ...) ≤ (⨆ x, ...)`
      apply iSup_le
      intro y
      -- We use `convert` to handle the substitution of `e_homeo y` with `x`.
      convert le_iSup (fun x' => ringKrullDim (X.presheaf.stalk x'.val)) (e_homeo y)

  rw [rhs_eq]

  -- The goal is now in the correct form, with everything in terms of `Y`.
  -- `topologicalKrullDim Y.carrier = ⨆ (y : Y.carrier), ringKrullDim (X.presheaf.stalk (e_homeo y))`

  -- The LHS is now `topologicalKrullDim Y.carrier`, which is `schemeDim Y`.
  change schemeDim Y = _
  -- By construction, `Y` is an affine scheme.
  let R := Scheme.Γ.obj (Opposite.op Y)
  let R_iso_spec : Y ≅ Spec (Scheme.Γ.obj (Opposite.op Y)) := Scheme.isoSpec Y

  -- We prove `schemeDim Y = ringKrullDim R` directly.
  unfold schemeDim
  -- An isomorphism of schemes provides a homeomorphism of the underlying spaces.
  let h_homeo : Y.carrier ≃ₜ (Spec (Scheme.Γ.obj (Opposite.op Y))).carrier :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso R_iso_spec)
  -- Since the spaces are homeomorphic, their topological Krull dimensions are equal.
  rw [IsHomeomorph.topologicalKrullDim_eq h_homeo h_homeo.isHomeomorph]
  -- Now, by the theorem you provided, the topological dimension of the prime spectrum
  -- is the same as the ring's Krull dimension.
  -- The goal's LHS is `topologicalKrullDim ↥(Spec R)`.
  -- We use `change` to make the definitional equality `↥(Spec R) = PrimeSpectrum R` explicit.
  change topologicalKrullDim (PrimeSpectrum (Scheme.Γ.obj (Opposite.op Y))) = _

  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]

  let h_homeo_affine : Y.carrier ≃ₜ (Spec R).carrier := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso R_iso_spec)
  -- The goal is `ringKrullDim R = ⨆ y, ringKrullDim (X.presheaf.stalk ↑(e_homeo y))`
  -- We'll prove this by showing the RHS is equal to the LHS.
  -- `eq_comm` swaps the sides to make the `calc` block more natural.
  rw [eq_comm]


  -- We now show that the supremum of the Krull dimensions of the stalks over the affine
  -- open `Y` is equal to the Krull dimension of its coordinate ring `R`.
  calc
    -- Start with the supremum over points in Y, mapped to X.
    ⨆ y, ringKrullDim (X.presheaf.stalk (e_homeo y).val)

    -- Step 1: The stalk of X at a point in an open subscheme Y is isomorphic to the stalk of Y.
    _ = ⨆ y, ringKrullDim (Y.presheaf.stalk y) := by
      apply iSup_congr; intro y
      have h_point_eq : (e_homeo y).val = f.base y :=
        congr_fun (congr_arg (fun g => g.base) (Scheme.Hom.isoOpensRange_hom_ι f)) y
      rw [h_point_eq]

      -- The morphism f.stalkMap y is an isomorphism, which we turn into a RingEquiv.
      -- Lean finds the `IsOpenImmersion.stalk_iso` instance automatically.
      exact RingEquiv.ringKrullDim (CategoryTheory.Iso.commRingCatIsoToRingEquiv
        (CategoryTheory.asIso (f.stalkMap y)))

    -- Step 2: Since Y ≅ Spec R, we can change the supremum over Y to one over Spec R.
    _ = ⨆ p : PrimeSpectrum R, ringKrullDim ((Spec R).presheaf.stalk p) := by
      -- First, we show that the supremum over Y's stalks is equal to the supremum
      -- over Spec R's stalks (still indexed by y ∈ Y).
      have h_sup_eq : (⨆ y, ringKrullDim (Y.presheaf.stalk y)) =
          (⨆ y, ringKrullDim ((Spec R).presheaf.stalk (h_homeo_affine y))) := by
        apply iSup_congr; intro y
        -- The scheme isomorphism `R_iso_spec : Y ≅ Spec R` has an underlying morphism `R_iso_spec.hom`,
        -- which induces an isomorphism on stalks.
        let stalk_map := (R_iso_spec.hom).stalkMap y
        -- Since `R_iso_spec.hom` is an iso, `stalk_map` is an iso. We get the RingEquiv.
        let stalk_equiv := CategoryTheory.Iso.commRingCatIsoToRingEquiv (CategoryTheory.asIso stalk_map)
        -- stalk_equiv maps from Spec R's stalk to Y's stalk. We need its inverse.
        exact (RingEquiv.ringKrullDim stalk_equiv.symm)

      -- Now, we apply this equality to the previous step's result.
      rw [h_sup_eq]

      -- Finally, we re-index the supremum from `y` in `Y` to `p` in `Spec R`
      -- using the homeomorphism `h_homeo_affine`.
      rw [h_homeo_affine.toEquiv.iSup_congr]
      rfl
      exact fun x ↦ rfl

    -- Step 3: The stalk of Spec R at a prime ideal `p` is the localization `R_p`.
    _ = ⨆ p : PrimeSpectrum R, ringKrullDim (Localization.AtPrime p.asIdeal) := by
      apply iSup_congr; intro p
      -- The isomorphism is defined directly in `StructureSheaf.lean` as `stalkIso`.
      -- We must convert this `Iso` from `CommRingCat` into a `RingEquiv`.
      let stalk_iso := AlgebraicGeometry.StructureSheaf.stalkIso R p
      let stalk_equiv := CategoryTheory.Iso.commRingCatIsoToRingEquiv stalk_iso
      exact RingEquiv.ringKrullDim stalk_equiv

    -- Step 4: The Krull dimension of a ring is the supremum of the dimensions of its localizations.
    _ = ringKrullDim R := by

      -- We must handle the case where the spectrum is empty (e.g., for the zero ring).
      cases isEmpty_or_nonempty (PrimeSpectrum R)

      · -- Case 1: The spectrum is empty.
        case inl h_empty =>
          haveI : IsEmpty (PrimeSpectrum R) := h_empty
          -- If the spectrum is empty, the LHS is a supremum over an empty set, which is defined as ⊥ (bottom).
          rw [iSup_of_empty]
          rw [ringKrullDim, krullDim_eq_bot]


      · -- Case 2: The spectrum is non-empty.
        case inr h_nonempty =>
          haveI : Nonempty (PrimeSpectrum R) := h_nonempty
          -- A direct proof can be more robust. We start by swapping the goal
          -- with `apply Eq.symm` to work on the simpler `ringKrullDim R` side first.
          apply Eq.symm

          -- Current Goal: ringKrullDim R = ⨆ p, ringKrullDim (Localization.AtPrime p.asIdeal)

          -- First, we express `ringKrullDim R` as the supremum of the heights of all prime ideals.
          -- `ringKrullDim` is defined as `Order.krullDim`, which is equal to `⨆ p, Order.height p`.
          rw [ringKrullDim, Order.krullDim_eq_iSup_height]

          -- Current Goal: (⨆ p, Order.height p) = ⨆ p, ringKrullDim (Localization.AtPrime p.asIdeal)

          -- Now that both sides are suprema over the same set, we just need to prove
          -- that the expressions inside are equal for any given prime `p`.
          apply iSup_congr
          intro p
          -- Current Goal for an arbitrary prime p:
          -- Order.height p = ringKrullDim (Localization.AtPrime p.asIdeal)

          -- We use the key theorem to rewrite the RHS.

          -- We explicitly state the rewrite rule we want to use. This helps Lean's
          -- typeclass inference find the required `IsLocalization.AtPrime` instance.
          have h_dim_eq_height : ringKrullDim (Localization.AtPrime p.asIdeal) = p.asIdeal.height := by
            apply IsLocalization.AtPrime.ringKrullDim_eq_height

          rw [h_dim_eq_height]

          -- Current Goal: Order.height p = p.asIdeal.height

          -- Finally, we use the lemmas from your file to show that these two notions
          -- of height are equivalent for a prime ideal.
          rw [Ideal.height_eq_primeHeight, Ideal.primeHeight]

          -- The goal is now `Order.height p = Order.height ⟨p.asIdeal, p.isPrime⟩`,
          -- which is true by definition, so the proof is complete.






-- Main theorem statement combining all parts
theorem thm_scheme_dim :
  (∀ (X : Type*) [TopologicalSpace X] (Y : Set X),
    topologicalKrullDim Y ≤ topologicalKrullDim X) ∧
  (∀ (X : Type*) [TopologicalSpace X] (Y : Set X),
    IsIrreducible (Set.univ : Set X) →
    topologicalKrullDim X ≠ ⊤ →
    IsClosed Y → Y ⊂ Set.univ → Y.Nonempty → -- This hypothesis was missing
    topologicalKrullDim Y < topologicalKrullDim X) ∧
  (∀ (X : Type*) [TopologicalSpace X] (ι : Type*) (U : ι → Set X),
    (∀ i, IsOpen (U i)) → (⋃ i, U i = Set.univ) →
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (U i)) ∧
  (∀ (X : Type*) [TopologicalSpace X],
    topologicalKrullDim X = ⨆ (Y ∈ irreducibleComponents X), topologicalKrullDim Y) ∧
  (∀ (X : Scheme), schemeDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x)) := by
  exact ⟨top_KrullDim_subspace_le, topological_dim_proper_closed_subset_lt,
         topological_dim_open_cover, topological_dim_irreducible_components,
         scheme_dim_eq_sup_local_rings⟩







