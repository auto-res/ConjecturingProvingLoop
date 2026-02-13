

theorem Topology.P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P3 A ↔ IsOpen (A : Set X) := by
  have h₁ := Topology.P3_iff_P2_of_isClosed (A := A) hA_closed
  have h₂ := Topology.P2_iff_isOpen_of_isClosed (A := A) hA_closed
  simpa using h₁.trans h₂