

theorem P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ Topology.P2 A := by
  have h₁ : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_isOpen (A := A) hA
  have h₂ : Topology.P3 A ↔ Topology.P2 A :=
    Topology.P3_iff_P2_of_isOpen (A := A) hA
  exact h₁.trans h₂