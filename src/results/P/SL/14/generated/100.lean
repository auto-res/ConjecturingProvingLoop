

theorem Topology.compl_satisfies_P1_P2_P3_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P1 (Aᶜ) ∧ Topology.P2 (Aᶜ) ∧ Topology.P3 (Aᶜ) := by
  have hOpen : IsOpen (Aᶜ) := hA_closed.isOpen_compl
  exact Topology.isOpen_satisfies_P1_P2_P3 (X := X) (A := Aᶜ) hOpen