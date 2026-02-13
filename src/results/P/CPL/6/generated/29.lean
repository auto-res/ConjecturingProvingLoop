

theorem P3_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Topology.P3 (Aᶜ) := by
  intro hA_closed
  have h_open : IsOpen (Aᶜ) := hA_closed.isOpen_compl
  exact P3_of_open (A := Aᶜ) h_open