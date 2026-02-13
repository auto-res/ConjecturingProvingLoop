

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (A : Set X) = Set.univ) :
    Topology.P2 (X := X) A := by
  dsimp [Topology.P2]
  intro x _hxA
  -- First, compute `interior (closure (interior A))`.
  have hint :
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
    have h_closure : closure (interior (A : Set X)) = (Set.univ : Set X) := by
      simpa [h] using closure_univ
    simpa [h_closure, interior_univ]
  -- The desired membership is now immediate.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [hint] using this