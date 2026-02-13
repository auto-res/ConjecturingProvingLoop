

theorem Topology.P2_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hxA
  -- Since `interior A` is dense, its closure is the whole space.
  have h_closure : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  -- Consequently, the interior of this closure is also the whole space.
  have h_int : interior (closure (interior A)) = (Set.univ : Set X) := by
    simpa [h_closure] using
      (interior_univ : interior (Set.univ : Set X) = Set.univ)
  -- Any point of `A` is therefore in `interior (closure (interior A))`.
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h_int] using this