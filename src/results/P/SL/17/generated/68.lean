

theorem Topology.closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  -- Step 1: `interior A ⊆ interior (closure A)`
  have h_int : interior A ⊆ interior (closure A) := by
    apply interior_mono
    exact subset_closure
  -- Step 2: Apply `closure_mono` to get the desired inclusion
  exact closure_mono h_int