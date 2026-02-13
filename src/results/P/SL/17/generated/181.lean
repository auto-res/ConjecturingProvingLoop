

theorem Topology.P3_of_interior_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : interior (closure A) = (Set.univ : Set X)) :
    Topology.P3 A := by
  unfold Topology.P3
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h] using this