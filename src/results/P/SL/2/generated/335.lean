

theorem Topology.closure_eq_closure_interior_union_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = closure (interior A) ∪ frontier (A : Set X) := by
  -- We prove the two inclusions separately.
  apply Set.Subset.antisymm
  · -- `⊆` direction
    intro x hxClA
    -- Case distinction on whether `x` lies in `interior A`.
    by_cases hxIntA : x ∈ interior (A : Set X)
    · -- If `x ∈ interior A`, then `x ∈ closure (interior A)`.
      have hxClInt : (x : X) ∈ closure (interior A) :=
        subset_closure hxIntA
      exact Or.inl hxClInt
    · -- Otherwise `x ∉ interior A`; since `x ∈ closure A`, `x` is in the frontier.
      have hxFront : (x : X) ∈ frontier (A : Set X) :=
        And.intro hxClA hxIntA
      exact Or.inr hxFront
  · -- `⊇` direction
    intro x hxUnion
    cases hxUnion with
    | inl hxClInt =>
        -- `closure (interior A) ⊆ closure A`
        exact
          (Topology.closure_interior_subset_closure (A := A)) hxClInt
    | inr hxFront =>
        -- By definition of the frontier, `x ∈ closure A`.
        exact hxFront.1