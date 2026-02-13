

theorem Topology.closure_eq_closureInterior_union_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) = closure (interior A) ∪ frontier A := by
  classical
  ext x
  constructor
  · intro hx_cl
    by_cases hx_clInt : x ∈ closure (interior A)
    · exact Or.inl hx_clInt
    ·
      -- Since `x ∉ interior A` and `x ∈ closure A`, it lies in the frontier.
      have hx_not_int : x ∉ interior A := by
        intro hx_int
        have : x ∈ closure (interior A) := subset_closure hx_int
        exact hx_clInt this
      exact Or.inr ⟨hx_cl, hx_not_int⟩
  · intro hx_union
    cases hx_union with
    | inl hx_clInt =>
        have h_subset : closure (interior A) ⊆ closure A :=
          closure_mono (interior_subset : interior A ⊆ A)
        exact h_subset hx_clInt
    | inr hx_front =>
        exact hx_front.1