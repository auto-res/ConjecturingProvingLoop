

theorem Topology.P3_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure A)) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  have hx_closure : (x : X) ∈ closure A := subset_closure hx
  simpa [h_open.interior_eq] using hx_closure