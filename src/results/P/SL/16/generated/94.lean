

theorem Topology.closed_compl_satisfies_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    Topology.P1 (X := X) (Aᶜ) ∧
      Topology.P2 (X := X) (Aᶜ) ∧
      Topology.P3 (X := X) (Aᶜ) := by
  have hOpen : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hClosed
  exact Topology.isOpen_satisfies_P1_P2_P3 (X := X) (A := Aᶜ) hOpen