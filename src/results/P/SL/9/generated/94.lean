

theorem Topology.closure_diff_interior_subset {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A \ interior A) ⊆ closure A \ interior A := by
  simpa using
    (closure_diff_subset_of_isOpen (s := A) (t := interior A) isOpen_interior)