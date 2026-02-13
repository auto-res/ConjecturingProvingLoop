

theorem Topology.P1_iff_P2_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_dense : closure (interior A : Set X) = Set.univ) :
    Topology.P1 (X := X) A ↔ Topology.P2 (X := X) A := by
  -- Both `P1` and `P2` hold unconditionally under the density assumption.
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P1_of_dense_interior (X := X) (A := A) h_dense
  have hP2 : Topology.P2 (X := X) A :=
    Topology.P2_of_dense_interior (X := X) (A := A) h_dense
  -- Assemble the equivalence from the two unconditional facts.
  constructor
  · intro _; exact hP2
  · intro _; exact hP1