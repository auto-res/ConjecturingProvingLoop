

theorem P1_univ {X : Type*} [TopologicalSpace X] : Topology.P1 (Set.univ : Set X) := by
  dsimp [Topology.P1]
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P2_univ {X : Type*} [TopologicalSpace X] : Topology.P2 (Set.univ : Set X) := by
  dsimp [Topology.P2]
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_univ {X : Type*} [TopologicalSpace X] : Topology.P3 (Set.univ : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P3_of_compact_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsCompact A) (h_dense : Dense A) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  have hclosure : closure (A : Set X) = (Set.univ : Set X) := by
    simpa using h_dense.closure_eq
  simpa [hclosure, interior_univ] using (Set.mem_univ x)