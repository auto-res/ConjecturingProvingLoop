

theorem Topology.isOpen_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → Topology.P1 A := by
  intro hA
  intro x hxA
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hxA
  exact subset_closure hx_int