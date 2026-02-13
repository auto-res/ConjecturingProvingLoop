

theorem isClosed_imp_P1_compl {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P1 (Aᶜ) := by
  have hOpen : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hA_closed
  simpa using Topology.isOpen_imp_P1 (X := X) (A := Aᶜ) hOpen