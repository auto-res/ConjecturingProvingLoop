

theorem Topology.P2_of_closure_interior_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior A) = (Set.univ : Set X) → Topology.P2 A := by
  intro hEq
  intro x hxA
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hEq, interior_univ] using this