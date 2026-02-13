

theorem Topology.P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Dense A) : Topology.P3 (A := A) := by
  dsimp [Topology.P3]
  intro x hxA
  simpa [hA.closure_eq] using (Set.mem_univ x)