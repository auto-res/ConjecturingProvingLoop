

theorem Topology.interior_union_closureDiffInterior_eq_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∪ (closure A \ interior A) = closure A := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hx_int =>
        exact (Topology.interior_subset_closure (A := A)) hx_int
    | inr hx_diff =>
        exact hx_diff.1
  · intro hx_cl
    by_cases hx_int : x ∈ interior (A : Set X)
    · exact Or.inl hx_int
    · exact Or.inr ⟨hx_cl, hx_int⟩