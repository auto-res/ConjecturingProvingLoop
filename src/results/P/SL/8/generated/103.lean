

theorem denseInterior_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 (closure A) := by
  dsimp [Topology.P1]
  -- From the density of `interior A`, we have `closure A = univ`.
  have h_closure_univ : closure A = (Set.univ : Set X) :=
    closure_eq_univ_of_denseInterior (X := X) (A := A) h_dense
  -- Consequently, `closure (interior (closure A))` is also `univ`.
  have h_target : closure (interior (closure A)) = (Set.univ : Set X) := by
    have h_int : interior (closure A) = (Set.univ : Set X) := by
      simpa [h_closure_univ, interior_univ]
    have h' : closure (interior (closure A)) = closure (Set.univ : Set X) := by
      simpa [h_int]
    simpa [closure_univ] using h'
  -- Establish the required inclusion.
  intro x _hx
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_target] using this