

theorem Topology.self_diff_frontier_eq_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    A \ frontier A = interior A := by
  classical
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxA, hNotFront⟩
    by_cases hInt : x ∈ interior A
    · exact hInt
    ·
      have hFront : x ∈ frontier A := And.intro (subset_closure hxA) hInt
      exact (hNotFront hFront).elim
  · intro hxInt
    have hxA : x ∈ A := interior_subset hxInt
    have hNotFront : x ∉ frontier A := by
      intro hFront
      exact hFront.2 hxInt
    exact And.intro hxA hNotFront