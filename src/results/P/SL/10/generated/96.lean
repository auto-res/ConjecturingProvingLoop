

theorem Topology.closure_interior_iUnion_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    (⋃ i, closure (interior (A i))) ⊆ closure (interior (⋃ i, A i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- Establish the inclusion needed to transfer `hx_i`.
  have h_closure :
      closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
    -- First, relate the interiors through monotonicity.
    have h_int : interior (A i) ⊆ interior (⋃ j, A j) := by
      have h_subset : (A i) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_subset
    -- Taking closures preserves the inclusion.
    exact closure_mono h_int
  exact h_closure hx_i