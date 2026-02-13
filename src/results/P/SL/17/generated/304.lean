

theorem Topology.closure_interior_union_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ∪ frontier A = closure A := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl h_cl_int =>
        -- `closure (interior A)` is contained in `closure A`
        have h_sub : closure (interior A) ⊆ closure A :=
          closure_mono (interior_subset : interior A ⊆ A)
        exact h_sub h_cl_int
    | inr h_front =>
        -- Points in the frontier of `A` lie in `closure A`
        exact h_front.1
  · intro hx_clA
    by_cases h_intA : x ∈ interior A
    · -- If `x ∈ interior A`, then it is in `closure (interior A)`
      have : x ∈ closure (interior A) := subset_closure h_intA
      exact Or.inl this
    · -- Otherwise, `x` belongs to the frontier of `A`
      have : x ∈ frontier A := And.intro hx_clA h_intA
      exact Or.inr this