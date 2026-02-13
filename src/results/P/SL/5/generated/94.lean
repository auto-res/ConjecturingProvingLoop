

theorem interior_closure_eq_univ_implies_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : interior (closure (A : Set X)) = Set.univ) :
    Topology.P3 (X := X) A := by
  dsimp [Topology.P3] at *
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h] using this