

theorem P3_iff_P2_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 (A : Set X) ↔ Topology.P2 A := by
  have h₁ := Topology.P3_iff_open_of_closed (A := A) hA
  have h₂ := Topology.P2_iff_open_of_closed (A := A) hA
  simpa using (h₁.trans h₂.symm)