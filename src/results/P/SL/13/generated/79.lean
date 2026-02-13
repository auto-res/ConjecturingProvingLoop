

theorem Topology.dense_implies_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_dense : Dense (A : Set X)) :
    Topology.P2 (X := X) (closure (A : Set X)) := by
  have h_closure_univ : closure (A : Set X) = (Set.univ : Set X) := hA_dense.closure_eq
  simpa [h_closure_univ] using (Topology.P2_univ (X := X))