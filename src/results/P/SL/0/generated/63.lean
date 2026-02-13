

theorem P2_compl_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 (Aᶜ) := by
  have hOpen : IsOpen ((Aᶜ) : Set X) := hA.isOpen_compl
  exact (Topology.isOpen_has_all_Ps (X := X) (A := (Aᶜ : Set X)) hOpen).2.1