

theorem Topology.P1_compl_iff_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P1 (Aᶜ) ↔ IsOpen (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ) := by
    simpa using (isOpen_compl_iff).2 hA
  constructor
  · intro _; exact hOpen
  · intro hOpenCompl
    exact Topology.P1_of_isOpen (A := Aᶜ) hOpenCompl