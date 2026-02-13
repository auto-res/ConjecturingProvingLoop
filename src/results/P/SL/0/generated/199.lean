

theorem compl_closed_has_all_Ps {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P1 (Aᶜ) ∧ Topology.P2 (Aᶜ) ∧ Topology.P3 (Aᶜ) := by
  have hOpen : IsOpen ((Aᶜ) : Set X) := hA.isOpen_compl
  exact Topology.isOpen_has_all_Ps (X := X) (A := (Aᶜ : Set X)) hOpen