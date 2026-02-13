

theorem Topology.P1_P2_P3_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P1 (Aᶜ) ∧ Topology.P2 (Aᶜ) ∧ Topology.P3 (Aᶜ) := by
  have hOpen : IsOpen (Aᶜ) := hA.isOpen_compl
  simpa using (Topology.IsOpen_P1_P2_P3 (A := Aᶜ) hOpen)