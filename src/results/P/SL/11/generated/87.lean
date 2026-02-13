

theorem P123_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  exact
    ⟨Topology.P1_of_dense_interior (A := A) hDense,
      Topology.P2_of_dense_interior (A := A) hDense,
      Topology.P3_of_dense_interior (A := A) hDense⟩