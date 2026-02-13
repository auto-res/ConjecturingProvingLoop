

theorem P123_complement_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P1 (Aᶜ) ∧ Topology.P2 (Aᶜ) ∧ Topology.P3 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ : Set X) := hA_closed.isOpen_compl
  -- Apply the combined property for open sets.
  simpa using Topology.P123_of_open (A := Aᶜ) hOpen