

theorem closed_P1_compl_iff_P2_compl {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P1 (Aᶜ) ↔ Topology.P2 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hA_open : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hA_closed
  -- Apply the existing equivalence for open sets.
  simpa using Topology.isOpen_P1_iff_P2 (X := X) (A := Aᶜ) hA_open