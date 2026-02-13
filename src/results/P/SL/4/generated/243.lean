

theorem closure_eq_closureInterior_union_frontier {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure A = closure (interior A) ∪ frontier A := by
  ext x
  constructor
  · intro hx
    by_cases hInt : x ∈ interior A
    · -- `x` is an interior point of `A`
      have hx' : x ∈ closure (interior A) := subset_closure hInt
      exact Or.inl hx'
    · -- `x` is not an interior point of `A`, hence it lies in the frontier
      have hFront : x ∈ frontier A := by
        -- `frontier A = closure A \ interior A`
        have : x ∈ closure A ∧ x ∉ interior A := And.intro hx hInt
        simpa [frontier, Set.diff_eq] using this
      exact Or.inr hFront
  · intro h
    cases h with
    | inl hClInt =>
        -- `closure (interior A)` is contained in `closure A`
        have hSub : closure (interior A) ⊆ closure A :=
          closure_interior_subset_closure (A := A)
        exact hSub hClInt
    | inr hFront =>
        -- Points of the frontier belong to `closure A`
        exact hFront.1