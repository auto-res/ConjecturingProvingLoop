

theorem Topology.P1_of_interior_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : interior (A : Set X) = Set.univ) :
    Topology.P1 (X := X) A := by
  dsimp [Topology.P1]
  intro x _
  -- Since `interior A = univ`, its closure is also `univ`, so every point belongs to it.
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h, closure_univ] using this