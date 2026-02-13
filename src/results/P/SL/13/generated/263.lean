

theorem Topology.closure_interior_union_closure_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (A : Set X)) ∪ closure A = closure A := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inr h_clA => exact h_clA
    | inl h_clIntA =>
        exact
          (Topology.closure_interior_subset_closure (X := X) (A := A)) h_clIntA
  · intro hx
    exact Or.inr hx