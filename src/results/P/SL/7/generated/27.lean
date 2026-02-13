

theorem Topology.P2_closed_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P2 A ↔ IsOpen A := by
  have h₁ : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isClosed (A := A) hA
  have h₂ : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_closed_iff_isOpen (A := A) hA
  simpa using h₁.trans h₂