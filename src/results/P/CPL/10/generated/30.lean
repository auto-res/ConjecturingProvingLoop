

theorem P1_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hP3 : Topology.P3 A) : Topology.P1 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    have : x ∈ interior (closure A) := hP3 hx
    simpa [hA.closure_eq] using this
  exact subset_closure hx_int