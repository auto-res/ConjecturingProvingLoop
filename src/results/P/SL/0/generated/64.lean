

theorem P3_compl_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 (Aᶜ) := by
  have hOpen : IsOpen ((Aᶜ) : Set X) := hA.isOpen_compl
  exact (Topology.isOpen_implies_P3 (X := X) (A := (Aᶜ : Set X))) hOpen