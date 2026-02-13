

theorem Topology.P1_dense_implies_closure_interior_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A → Dense A → closure (interior A) = (Set.univ : Set X) := by
  intro hP1 hDense
  -- `P1 A` gives `closure (interior A) = closure A`.
  have h₁ : closure (interior A) = closure A :=
    Topology.P1_implies_closure_interior_eq_closure (A := A) hP1
  -- Density of `A` yields `closure A = univ`.
  have h₂ : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  -- Combine the two equalities.
  simpa [h₂] using h₁