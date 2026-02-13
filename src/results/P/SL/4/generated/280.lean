

theorem diff_frontier_eq_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    A \ frontier A = interior A := by
  ext x
  constructor
  · intro hx
    have hxA : x ∈ A := hx.1
    have hNotFront : x ∉ frontier A := hx.2
    -- If `x` were not in `interior A`, it would lie in the frontier,
    -- because points of `A` outside `interior A` belong to `frontier A`.
    by_cases hxInt : x ∈ interior A
    · exact hxInt
    · have hxFront : x ∈ frontier A := by
        -- `x ∈ closure A` since `A ⊆ closure A`.
        have hxCl : x ∈ closure A := subset_closure hxA
        exact And.intro hxCl hxInt
      exact (hNotFront hxFront).elim
  · intro hxInt
    have hxA : x ∈ A := interior_subset hxInt
    -- Points of `interior A` are not in the frontier.
    have hNotFront : x ∉ frontier A := by
      intro hFront
      have : x ∈ (interior A)ᶜ :=
        (frontier_subset_compl_interior (X := X) (A := A)) hFront
      exact this hxInt
    exact And.intro hxA hNotFront