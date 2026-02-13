

theorem P1_iff_P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : Topology.P1 A ↔ Topology.P2 A := by
  -- The density of `interior A` implies that its closure is the whole space.
  have h_closure : closure (interior (A : Set X)) = (Set.univ : Set X) := by
    simpa using h.closure_eq
  -- Hence `P2 A` holds unconditionally.
  have hP2_dense : Topology.P2 A := by
    dsimp [Topology.P2]
    intro x _
    simpa [h_closure, interior_univ] using (by
      simp : x ∈ (Set.univ : Set X))
  -- Establish the equivalence.
  constructor
  · intro _hP1
    exact hP2_dense
  · intro hP2
    exact P2_implies_P1 hP2