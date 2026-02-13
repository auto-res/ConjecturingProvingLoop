

theorem denseInterior_imp_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P2 (closure A) := by
  dsimp [Topology.P2]
  -- First, note that `closure A = univ`.
  have h_closure : closure A = (Set.univ : Set X) :=
    closure_eq_univ_of_denseInterior (X := X) (A := A) h_dense
  -- Next, compute `interior (closure (interior (closure A))) = univ`.
  have h_target :
      interior (closure (interior (closure A))) = (Set.univ : Set X) := by
    -- `interior (closure A)` is already `univ`.
    have h_int : interior (closure A) = (Set.univ : Set X) := by
      simpa [h_closure, interior_univ]
    -- Hence its closure is also `univ`.
    have h_cl : closure (interior (closure A)) = (Set.univ : Set X) := by
      simpa [h_int, closure_univ]
    -- Taking the interior once more yields `univ`.
    simpa [h_cl, interior_univ] using rfl
  -- Establish the required inclusion.
  intro x _hx
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_closure, h_target] using this