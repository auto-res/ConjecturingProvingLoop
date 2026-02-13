

theorem Topology.P3_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : IsOpen (closure A)) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  have hx_closure : (x : X) ∈ closure A := subset_closure hxA
  simpa [h.interior_eq] using hx_closure