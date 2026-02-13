

theorem Topology.closure_interior_diff_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A \ B)) ⊆ closure (interior A) := by
  have h_diff_subset : (A \ B) ⊆ A := Set.diff_subset
  have h_int_subset : interior (A \ B) ⊆ interior A :=
    interior_mono h_diff_subset
  exact closure_mono h_int_subset