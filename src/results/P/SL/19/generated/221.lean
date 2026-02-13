

theorem Topology.P3_of_interior_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure A) = (Set.univ : Set X)) :
    Topology.P3 (A := A) := by
  dsimp [Topology.P3]
  intro x _
  have : (x : X) ∈ (Set.univ : Set X) := by
    exact Set.mem_univ x
  simpa [h] using this