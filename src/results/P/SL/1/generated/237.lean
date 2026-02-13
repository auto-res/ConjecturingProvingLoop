

theorem Topology.closure_interior_eq_closure_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Dense (interior A)) :
    closure (interior A) = closure A := by
  have h₁ : closure (interior A) = (Set.univ : Set X) := h.closure_eq
  have h₂ : closure A = (Set.univ : Set X) :=
    Topology.closure_eq_univ_of_dense_interior (A := A) h
  simpa [h₁, h₂]