

theorem closure_diff_frontier_eq_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure A \ frontier A = interior A := by
  ext x
  constructor
  · intro hx
    have hxCl : x ∈ closure A := hx.1
    have hNotFront : x ∉ frontier A := hx.2
    by_contra hNotInt
    have hFront : x ∈ frontier A := And.intro hxCl hNotInt
    exact hNotFront hFront
  · intro hxInt
    have hxCl : x ∈ closure A := subset_closure (interior_subset hxInt)
    have hNotFront : x ∉ frontier A := by
      intro hFront
      exact hFront.2 hxInt
    exact And.intro hxCl hNotFront