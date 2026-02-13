

theorem P2_complement_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P2 (X:=X) (Aᶜ) := by
  simpa using
    (P2_of_open (X := X) (A := Aᶜ) ((isOpen_compl_iff).2 hA))