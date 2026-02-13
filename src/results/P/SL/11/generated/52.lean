

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P2 A ↔ Topology.P3 A := by
  have h₁ : Topology.P2 A ↔ IsOpen A :=
    Topology.P2_iff_open_of_closed (A := A) hA
  have h₂ : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_iff_open_of_closed (A := A) hA
  simpa using h₁.trans h₂.symm