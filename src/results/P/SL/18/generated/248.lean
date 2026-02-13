

theorem P1_complement_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P1 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ : Set X) := hA_closed.isOpen_compl
  -- Apply the lemma asserting `P1` for open sets.
  exact Topology.P1_of_open hOpen