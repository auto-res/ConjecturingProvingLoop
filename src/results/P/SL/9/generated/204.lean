

theorem closure_eq_closureInterior_union_boundary
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = closure (interior A) ∪ (closure A \ interior A) := by
  ext x
  constructor
  · intro hx_clA
    by_cases hx_intA : x ∈ interior (A : Set X)
    · -- `x` is in the interior, hence in `closure (interior A)`.
      have : x ∈ closure (interior A) := by
        exact subset_closure hx_intA
      exact Or.inl this
    · -- `x` is not in the interior, so it belongs to the boundary part.
      exact Or.inr ⟨hx_clA, hx_intA⟩
  · intro hx_union
    cases hx_union with
    | inl hx_cl_int =>
        -- `closure (interior A)` is contained in `closure A`.
        have h_subset := Topology.closureInterior_subset_closure (A := A)
        exact h_subset hx_cl_int
    | inr hx_boundary =>
        exact hx_boundary.1