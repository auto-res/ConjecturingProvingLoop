

theorem Topology.interior_eq_self_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P2 (A := A) → interior A = A := by
  intro hP2
  have hP3 : Topology.P3 (A := A) := Topology.P2_implies_P3 (A := A) hP2
  exact Topology.interior_eq_self_of_isClosed_and_P3 (A := A) hA hP3