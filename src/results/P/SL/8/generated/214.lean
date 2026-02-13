

theorem isClosed_imp_P3_compl {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 (Aᶜ) := by
  have hA_open : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hA_closed
  simpa using Topology.isOpen_imp_P3 (X := X) (A := Aᶜ) hA_open