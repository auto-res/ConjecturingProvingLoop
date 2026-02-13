

theorem Topology.P2_iff_P1_of_isClopen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClopen A) :
    Topology.P2 A ↔ Topology.P1 A := by
  simpa using
    (Topology.P1_iff_P2_of_isOpen (A := A) hA.2).symm