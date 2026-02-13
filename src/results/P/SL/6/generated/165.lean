

theorem clopen_of_P2_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP2 : Topology.P2 (A : Set X)) :
    IsOpen A ∧ IsClosed (A : Set X) := by
  have hOpen : IsOpen (A : Set X) :=
    (Topology.open_of_P2_closed (A := A) hClosed) hP2
  exact And.intro hOpen hClosed