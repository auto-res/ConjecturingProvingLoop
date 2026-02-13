

theorem Topology.P2_iff_P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P2 A ↔ Topology.P3 A := by
  -- The density assumption forces both properties to hold unconditionally.
  have hP2 : Topology.P2 A := Topology.P2_of_dense_interior (A := A) hDense
  have hP3 : Topology.P3 A := Topology.P3_of_dense_interior (A := A) hDense
  constructor
  · intro _; exact hP3
  · intro _; exact hP2