

theorem P2_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (A : Set X) = (Set.univ : Set X)) :
    Topology.P2 (closure (A : Set X)) := by
  simpa [hDense] using (Topology.P2_univ (X := X))