

theorem P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) := by
  dsimp [Topology.P1]
  intro x _
  simpa [interior_univ, closure_univ] using (Set.mem_univ x)