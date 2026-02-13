

theorem Topology.closed_P2_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    Topology.P2 (X := X) A ↔ Topology.P3 (X := X) A := by
  have h₁ := Topology.closed_P2_iff_isOpen (X := X) (A := A) hClosed
  have h₂ := Topology.closed_P3_iff_isOpen (X := X) (A := A) hClosed
  exact h₁.trans h₂.symm