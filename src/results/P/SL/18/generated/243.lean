

theorem P2_complement_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ : Set X) := hA_closed.isOpen_compl
  exact Topology.P2_of_open (A := Aᶜ) hOpen