

theorem Topology.denseInterior_implies_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense (interior (A : Set X)) →
      closure (A : Set X) = (Set.univ : Set X) := by
  intro hDense
  -- First, relate `closure A` to `closure (interior A)` using the existing lemma.
  have h_eq :
      closure (A : Set X) = closure (interior A) :=
    Topology.closure_eq_closureInterior_of_denseInterior (X := X) (A := A) hDense
  -- Since `interior A` is dense, its closure is the whole space.
  have h_closure_int : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  -- Combine the two equalities.
  simpa [h_closure_int] using h_eq