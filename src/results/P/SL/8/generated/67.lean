

theorem interior_univ_imp_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_int : interior A = (Set.univ : Set X)) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  -- Compute `interior (closure (interior A))`
  have h_interior_closure :
      interior (closure (interior A)) = (Set.univ : Set X) := by
    have h_closure : closure (interior A) = (Set.univ : Set X) := by
      simpa [h_int, closure_univ]
    simpa [h_closure, interior_univ]
  -- The required inclusion is now trivial
  intro x hxA
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_interior_closure] using this