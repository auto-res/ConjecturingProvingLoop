

theorem Topology.interior_union_frontier_eq_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∪ frontier A = closure A := by
  classical
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hxInt =>
        -- Points of `interior A` are certainly in `closure A`.
        exact subset_closure (interior_subset hxInt)
    | inr hxFront =>
        -- The first component of `frontier` membership is `closure A`.
        exact hxFront.1
  · intro hxCl
    -- Split depending on whether `x` lies in `interior A`.
    by_cases hxInt : x ∈ interior (A : Set X)
    · exact Or.inl hxInt
    · exact Or.inr ⟨hxCl, hxInt⟩