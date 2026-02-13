

theorem Topology.iUnion_interior_closure_subset_interior_closure_iUnion
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    (⋃ i, interior (closure (A i)) : Set X) ⊆
      interior (closure (⋃ i, A i : Set X)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have h_sub :
      (interior (closure (A i)) : Set X) ⊆
        interior (closure (⋃ j, A j : Set X)) := by
    -- First, relate the closures of the sets.
    have h_closure :
        (closure (A i : Set X)) ⊆ closure (⋃ j, A j) := by
      have : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact closure_mono this
    -- Then, pass to interiors via monotonicity.
    exact interior_mono h_closure
  exact h_sub hx_i