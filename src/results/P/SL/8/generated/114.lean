

theorem denseInterior_imp_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P3 (closure A) := by
  -- We will show that `interior (closure A) = univ`, which makes `P3` trivial.
  have hIntUniv : interior (closure A) = (Set.univ : Set X) :=
    interior_closure_eq_univ_of_denseInterior (X := X) (A := A) h_dense
  -- Unfold `P3` for the set `closure A`.
  dsimp [Topology.P3]
  intro x hx
  -- Every point belongs to `univ`, and hence to `interior (closure A)`.
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [hIntUniv] using this