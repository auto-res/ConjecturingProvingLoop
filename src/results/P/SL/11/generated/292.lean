

theorem P1_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (A : Set X) = (Set.univ : Set X)) :
    Topology.P1 (closure (A : Set X)) := by
  simpa [hDense] using (Topology.P1_univ (X := X))