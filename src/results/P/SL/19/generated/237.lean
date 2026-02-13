

theorem Topology.isClosed_iff_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A ↔ closure A ⊆ A := by
  constructor
  · intro hClosed
    simpa [hClosed.closure_eq]
  · intro hSubset
    have hEq : closure A = A := Set.Subset.antisymm hSubset subset_closure
    simpa [hEq] using (isClosed_closure (s := A))