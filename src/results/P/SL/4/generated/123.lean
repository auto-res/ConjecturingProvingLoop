

theorem closed_eq_closure_interior_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P3 A → A = closure (interior A) := by
  intro hP3
  have h := Topology.closure_eq_closure_interior_of_P3_closed (A := A) hA hP3
  simpa [hA.closure_eq] using h