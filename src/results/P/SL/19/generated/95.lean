

theorem Topology.P3_of_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A = (Set.univ : Set X) → Topology.P3 (A := A) := by
  intro hDense
  dsimp [Topology.P3]
  intro x hx
  have hInt : interior (closure A) = (Set.univ : Set X) := by
    simpa [hDense, interior_univ]
  have hx_univ : x ∈ (Set.univ : Set X) := by
    exact Set.mem_univ x
  simpa [hInt] using hx_univ