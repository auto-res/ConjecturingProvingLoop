

theorem Topology.P2_of_denseInterior'
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hxA
  -- The closure of `interior A` is the whole space.
  have h_closure : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  -- Hence its interior is also the whole space.
  have : (x : X) ∈ interior (Set.univ : Set X) := by
    simpa [interior_univ]
  simpa [h_closure] using this