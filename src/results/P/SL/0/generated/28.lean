

theorem P2_iff_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 A ↔ Topology.P3 A := by
  have h₁ : Topology.P2 A ↔ IsOpen (A : Set X) :=
    Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hA
  have h₂ : Topology.P3 A ↔ IsOpen (A : Set X) :=
    Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA
  exact h₁.trans h₂.symm