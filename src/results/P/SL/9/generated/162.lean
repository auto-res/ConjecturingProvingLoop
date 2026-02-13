

theorem Topology.P3_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure (A : Set X))) : Topology.P3 (A := A) := by
  dsimp [Topology.P3]
  intro x hxA
  have hx_closure : x ∈ closure (A : Set X) := Set.subset_closure hxA
  simpa [h_open.interior_eq] using hx_closure