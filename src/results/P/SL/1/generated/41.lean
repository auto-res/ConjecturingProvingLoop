

theorem Topology.P2_iff_P3_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P2 A ↔ Topology.P3 A := by
  have h1 : Topology.P2 A ↔ IsOpen A :=
    Topology.P2_iff_isOpen_of_isClosed (A := A) hA
  have h2 : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_iff_isOpen_of_isClosed (A := A) hA
  simpa using h1.trans h2.symm