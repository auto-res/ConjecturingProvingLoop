

theorem P3_of_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A = Set.univ) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  simpa [h, interior_univ]

theorem P2_of_interior_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} (h : interior (closure (interior A)) = Set.univ) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hx
  simpa [h] using (Set.mem_univ x)