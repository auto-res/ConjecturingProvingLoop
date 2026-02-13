

theorem Topology.closure_iUnion_interior_subset_closureInterior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    closure (⋃ i, interior (A i) : Set X) ⊆
      closure (interior (⋃ i, A i)) := by
  -- First, prove the set inside the left‐hand closure is contained in the right‐hand interior.
  have h_subset : (⋃ i, interior (A i) : Set X) ⊆ interior (⋃ i, A i) := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hx_int⟩
    -- `A i` is contained in the union, hence its interior is contained in the interior of the union.
    have h_int_mono :
        interior (A i : Set X) ⊆ interior (⋃ j, A j) := by
      have h_subset' : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_subset'
    exact h_int_mono hx_int
  -- Taking closures preserves inclusions, yielding the desired result.
  exact closure_mono h_subset