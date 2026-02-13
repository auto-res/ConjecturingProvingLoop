

theorem dense_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure A = (Set.univ : Set X)) :
    Topology.P1 (closure A) := by
  dsimp [Topology.P1]
  intro x _hx
  -- First, compute `interior (closure A) = univ`.
  have h_int : interior (closure A) = (Set.univ : Set X) := by
    simpa [h_dense, interior_univ]
  -- Consequently, `closure (interior (closure A)) = univ`.
  have h_cl : closure (interior (closure A)) = (Set.univ : Set X) := by
    simpa [h_int, closure_univ]
  -- The required membership is now trivial.
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_cl] using this