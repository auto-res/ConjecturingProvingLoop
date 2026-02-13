

theorem Topology.interior_eq_diff_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = A \ frontier A := by
  ext x
  constructor
  · intro hxInt
    have hxA : x ∈ A := interior_subset hxInt
    have hxNotFrontier : x ∉ frontier A := by
      intro hxFront
      -- `hxFront.2` asserts `x ∉ interior A`, contradicting `hxInt`.
      exact hxFront.2 hxInt
    exact And.intro hxA hxNotFrontier
  · intro hx
    rcases hx with ⟨hxA, hxNotFrontier⟩
    by_cases hxInt : x ∈ interior A
    · exact hxInt
    ·
      -- From `x ∈ A` we get `x ∈ closure A`.
      have hxClos : x ∈ closure A := subset_closure hxA
      -- Together with `hxInt : x ∉ interior A`, this places `x` in the frontier,
      -- contradicting `hxNotFrontier`.
      have hxFrontier : x ∈ frontier A := And.intro hxClos hxInt
      exact False.elim (hxNotFrontier hxFrontier)