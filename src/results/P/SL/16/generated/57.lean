

theorem Topology.isOpen_P1_iff_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) :
    Topology.P1 (X := X) A ↔ Topology.P2 (X := X) A := by
  have h₁ : Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A :=
    Topology.isOpen_P1_iff_P3 (X := X) (A := A) hOpen
  have h₂ : Topology.P2 (X := X) A ↔ Topology.P3 (X := X) A :=
    Topology.isOpen_P2_iff_P3 (X := X) (A := A) hOpen
  exact h₁.trans h₂.symm