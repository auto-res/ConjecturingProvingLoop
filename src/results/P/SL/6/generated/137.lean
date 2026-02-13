

theorem clopen_of_closed_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP3 : Topology.P3 (A : Set X)) :
    IsOpen A ∧ IsClosed (A : Set X) := by
  have hOpen : IsOpen (A : Set X) :=
    (Topology.open_of_P3_closed (A := A) hClosed) hP3
  exact And.intro hOpen hClosed