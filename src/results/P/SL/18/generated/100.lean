

theorem dense_of_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = Set.univ → Dense (A : Set X) := by
  intro hInt x
  -- Since `interior (closure A) = univ`, every point lies in this interior.
  have hx_int : (x : X) ∈ interior (closure (A : Set X)) := by
    have : (x : X) ∈ (Set.univ : Set X) := by
      trivial
    simpa [hInt] using this
  -- The interior is contained in the closure, yielding the desired density.
  exact (interior_subset : interior (closure (A : Set X)) ⊆ closure (A : Set X)) hx_int