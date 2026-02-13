

theorem dense_interior_satisfies_P1_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior (A : Set X)) = Set.univ) :
    Topology.P1 A ∧ Topology.P2 A := by
  -- First, note that the interior of the universal set is itself.
  have hInt : interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
    simpa [hDense] using (interior_univ : interior (Set.univ : Set X) = _)
  constructor
  · -- Establish `P1`.
    dsimp [Topology.P1]
    intro x hx
    have : x ∈ (Set.univ : Set X) := by
      simp
    simpa [hDense] using this
  · -- Establish `P2`.
    dsimp [Topology.P2]
    intro x hx
    have : x ∈ (Set.univ : Set X) := by
      simp
    simpa [hInt] using this