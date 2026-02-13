

theorem Topology.P3_of_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = (Set.univ : Set X) → Topology.P3 A := by
  intro hCl
  intro x hxA
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hCl, interior_univ] using this