

theorem clopen_of_closed_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP2 : Topology.P2 A) :
    IsClopen (A : Set X) := by
  refine ⟨hClosed, ?_⟩
  exact isOpen_of_closed_P2 (A := A) hClosed hP2