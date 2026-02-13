

theorem Topology.clopen_of_isClosed_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    IsOpen A ∧ IsClosed A := by
  have hOpen : IsOpen A :=
    Topology.isOpen_of_isClosed_and_P2 (X := X) (A := A) hA_closed hP2
  exact ⟨hOpen, hA_closed⟩