

theorem Topology.P3_iff_P1_of_isClopen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClopen A) :
    Topology.P3 A ↔ Topology.P1 A := by
  have hOpen : IsOpen A := hA.2
  simpa using
    (Topology.P1_iff_P3_of_isOpen (A := A) hOpen).symm