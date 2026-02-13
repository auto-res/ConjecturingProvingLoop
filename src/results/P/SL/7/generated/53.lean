

theorem Topology.P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior A) = (Set.univ : Set X)) : Topology.P3 A := by
  have hP2 : Topology.P2 A := Topology.P2_of_dense_interior (A := A) hA
  exact Topology.P2_implies_P3 hP2