

theorem Topology.closure_eq_closure_interior_of_subset
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure A ⊆ closure (interior A)) :
    closure A = closure (interior A) := by
  apply Set.Subset.antisymm
  · exact h
  · exact Topology.closure_interior_subset_closure (A := A)