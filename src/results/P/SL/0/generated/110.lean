

theorem P3_of_interior_closure_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior (closure (A : Set X)) = (Set.univ : Set X)) :
    Topology.P3 A := by
  dsimp [Topology.P3] at *
  intro x _
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [hInt] using hx_univ