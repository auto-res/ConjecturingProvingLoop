

theorem P3_of_interior_closure_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure (A : Set X)) = (Set.univ : Set X)) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  have hx_univ : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h] using hx_univ