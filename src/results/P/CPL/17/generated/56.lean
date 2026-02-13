

theorem P3_Union_open_sets {ι : Sort*} {X : Type*} [TopologicalSpace X] {U : ι → Set X} : (∀ i, IsOpen (U i)) → P3 (⋃ i, U i) := by
  intro hU_open
  have hP3_each : ∀ i, Topology.P3 (U i) := by
    intro i
    exact P3_of_open (A := U i) (hU_open i)
  simpa using (P3_iUnion (X := X) (f := U) hP3_each)

theorem P2_subset_exists_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → ∃ B, B ⊆ A ∧ P3 B := by
  intro hP2
  exact ⟨A, subset_rfl, P2_implies_P3 (A := A) hP2⟩

theorem P1_intersection_open_sets {X : Type*} [TopologicalSpace X] {A U : Set X} : IsOpen U → P1 A → P1 (A ∩ U) := by
  intro hU_open hP1A
  intro x hxAU
  -- Split the membership of `x`
  have hxA : x ∈ A := hxAU.1
  have hxU : x ∈ U := hxAU.2
  -- Use `P1` for `A`
  have hx_cl : x ∈ closure (interior A) := hP1A hxA
  -- Show that `x` belongs to `closure (interior (A ∩ U))`
  have : x ∈ closure (interior (A ∩ U)) := by
    -- Neighborhood characterization of closure for `interior A`
    have h_closure_prop := (mem_closure_iff).1 hx_cl
    -- Prove the analogous property for `interior (A ∩ U)`
    have h_prop :
        ∀ V, IsOpen V → x ∈ V → (V ∩ interior (A ∩ U)).Nonempty := by
      intro V hV_open hxV
      -- Work inside the open set `V ∩ U`
      have hVU_open : IsOpen (V ∩ U) := hV_open.inter hU_open
      have hxVU : x ∈ V ∩ U := ⟨hxV, hxU⟩
      -- From `x ∈ closure (interior A)` we get a point of `interior A`
      have h_nonempty : ((V ∩ U) ∩ interior A).Nonempty :=
        h_closure_prop (V ∩ U) hVU_open hxVU
      rcases h_nonempty with ⟨y, ⟨hyVU, hyIntA⟩⟩
      rcases hyVU with ⟨hyV, hyU⟩
      -- Show that `y ∈ interior (A ∩ U)`
      have h_subset :
          (interior A ∩ U : Set X) ⊆ interior (A ∩ U) := by
        -- `interior A ∩ U` is open and contained in `A ∩ U`
        have h_open_left : IsOpen (interior A ∩ U) :=
          (isOpen_interior).inter hU_open
        have h_left_sub : (interior A ∩ U : Set X) ⊆ A ∩ U := by
          intro z hz
          exact ⟨(interior_subset : interior A ⊆ A) hz.1, hz.2⟩
        exact interior_maximal h_left_sub h_open_left
      have hy_int : y ∈ interior (A ∩ U) := h_subset ⟨hyIntA, hyU⟩
      exact ⟨y, ⟨hyV, hy_int⟩⟩
    exact (mem_closure_iff).2 h_prop
  exact this

theorem P3_of_closed_dense_boundary {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Dense (frontier A) → P3 A := by
  intro hA_closed hDense
  -- `frontier A ⊆ A` because `A` is closed (`closure A = A`).
  have h_frontier_sub_A : (frontier A : Set X) ⊆ A := by
    intro y hy
    -- `frontier A ⊆ closure A`
    have h_mem_closure : (y : X) ∈ closure A :=
      (frontier_subset_closure) hy
    simpa [hA_closed.closure_eq] using h_mem_closure
  -- Hence the closure of the frontier is contained in `A`.
  have h_closure_frontier_sub_A :
      closure (frontier A : Set X) ⊆ A :=
    closure_minimal h_frontier_sub_A hA_closed
  -- But the frontier is dense, so its closure is the whole space.
  have h_closure_frontier_univ :
      closure (frontier A : Set X) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- Therefore `A` equals the whole space.
  have hA_univ : (A : Set X) = Set.univ := by
    apply Set.Subset.antisymm
    · exact Set.subset_univ _
    ·
      have : (Set.univ : Set X) ⊆ A := by
        simpa [h_closure_frontier_univ] using h_closure_frontier_sub_A
      exact this
  -- Consequently, `interior (closure A)` is the whole space.
  have h_int : interior (closure A) = (Set.univ : Set X) := by
    simpa [hA_closed.closure_eq, hA_univ, interior_univ]
  -- Establish `P3 A`.
  intro x hxA
  -- Rewrite the goal using the equalities obtained above.
  simpa [hA_closed.closure_eq, hA_univ, interior_univ] using hxA