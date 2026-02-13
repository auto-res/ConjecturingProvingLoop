

theorem interior_univ_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_int : interior A = (Set.univ : Set X)) :
    Topology.P3 A := by
  -- From `interior A = univ`, we deduce `closure (interior A) = univ`.
  have h_dense : closure (interior A) = (Set.univ : Set X) := by
    simpa [h_int, closure_univ]
  -- Apply the existing lemma for dense interior.
  exact Topology.denseInterior_imp_P3 (X := X) (A := A) h_dense