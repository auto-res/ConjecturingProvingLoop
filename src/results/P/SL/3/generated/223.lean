

theorem clopen_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP2 : Topology.P2 (A : Set X)) :
    IsClosed (A : Set X) ∧ IsOpen (A : Set X) := by
  exact ⟨hA_closed, isOpen_of_isClosed_and_P2 (A := A) hA_closed hP2⟩