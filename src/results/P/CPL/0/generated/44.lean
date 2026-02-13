

theorem P1_finset_iUnion {X : Type*} [TopologicalSpace X] {ι} (s : Finset ι) (u : ι → Set X) : (∀ i, i ∈ s → P1 (u i)) → P1 (⋃ i ∈ s, u i) := by
  intro hP1
  intro x hx
  -- Decompose the membership in the finite union.
  rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨hi, hxui⟩
  -- `P1` holds for `u i`.
  have hP1i : P1 (u i) := hP1 i hi
  have hx_cl : x ∈ closure (interior (u i : Set X)) := hP1i hxui
  -- Show the required inclusion of closures.
  have h_subset :
      closure (interior (u i : Set X))
        ⊆ closure (interior (⋃ j ∈ s, u j)) := by
    -- First, the corresponding inclusion for interiors.
    have h_int_subset :
        interior (u i : Set X)
          ⊆ interior (⋃ j ∈ s, u j) := by
      have h_set_subset : (u i : Set X) ⊆ ⋃ j ∈ s, u j := by
        intro y hy
        exact
          Set.mem_iUnion.2
            ⟨i, Set.mem_iUnion.2 ⟨hi, hy⟩⟩
      exact interior_mono h_set_subset
    -- Take closures.
    exact closure_mono h_int_subset
  exact h_subset hx_cl

theorem P2_finset_iUnion {X : Type*} [TopologicalSpace X] {ι} (s : Finset ι) (u : ι → Set X) : (∀ i, i ∈ s → P2 (u i)) → P2 (⋃ i ∈ s, u i) := by
  intro hP2
  intro x hx
  -- Decompose the membership in the finite union.
  rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨hi, hxui⟩
  -- `P2` holds for `u i`.
  have hP2i : P2 (u i) := hP2 i hi
  have hx_int : x ∈ interior (closure (interior (u i : Set X))) := hP2i hxui
  -- Show the required inclusion of the interiors of the closures.
  have h_subset :
      interior (closure (interior (u i : Set X))) ⊆
        interior (closure (interior (⋃ j ∈ s, u j))) := by
    -- Step 1: `interior (u i) ⊆ interior (⋃ j ∈ s, u j)`.
    have h_int_sub :
        interior (u i : Set X) ⊆ interior (⋃ j ∈ s, u j) := by
      have h_set_sub : (u i : Set X) ⊆ ⋃ j ∈ s, u j := by
        intro y hy
        exact
          Set.mem_iUnion.2
            ⟨i, Set.mem_iUnion.2 ⟨hi, hy⟩⟩
      exact interior_mono h_set_sub
    -- Step 2: take closures.
    have h_cl_sub :
        closure (interior (u i : Set X)) ⊆
          closure (interior (⋃ j ∈ s, u j)) :=
      closure_mono h_int_sub
    -- Step 3: take interiors again.
    exact interior_mono h_cl_sub
  exact h_subset hx_int

theorem P3_finset_iUnion {X : Type*} [TopologicalSpace X] {ι} (s : Finset ι) (u : ι → Set X) : (∀ i, i ∈ s → P3 (u i)) → P3 (⋃ i ∈ s, u i) := by
  intro hP3
  intro x hx
  -- Break membership in the finite union into its constituents.
  rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨hi, hxi⟩
  -- Apply `P3` to the chosen index.
  have hP3i : P3 (u i) := hP3 i hi
  have hx_int : x ∈ interior (closure (u i : Set X)) := hP3i hxi
  -- Show that the corresponding interior is included in the one for the union.
  have h_subset :
      interior (closure (u i : Set X)) ⊆
        interior (closure (⋃ j ∈ s, u j)) := by
    -- First, the inclusion for closures.
    have h_closure_sub :
        closure (u i : Set X) ⊆ closure (⋃ j ∈ s, u j) := by
      have h_set_sub : (u i : Set X) ⊆ ⋃ j ∈ s, u j := by
        intro y hy
        exact
          Set.mem_iUnion.2
            ⟨i, Set.mem_iUnion.2 ⟨hi, hy⟩⟩
      exact closure_mono h_set_sub
    -- Then apply monotonicity of `interior`.
    exact interior_mono h_closure_sub
  exact h_subset hx_int