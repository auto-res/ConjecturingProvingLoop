

theorem Topology.P1_interior_iff_P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ↔ Topology.P3 (interior A) := by
  simpa using
    ((Topology.P1_interior_iff_P2_interior (A := A)).trans
      ((Topology.P3_interior_iff_P2_interior (A := A)).symm))