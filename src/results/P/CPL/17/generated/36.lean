

theorem P3_interior_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} : interior (closure A) = Set.univ → Topology.P3 A := by
  intro h_eq
  intro x hxA
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h_eq] using this