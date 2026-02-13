

theorem inter_frontier_eq_diff_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    (A ∩ frontier A : Set X) = A \ interior A := by
  ext x
  constructor
  · intro hx
    exact And.intro hx.1 hx.2.2
  · intro hx
    have hx_cl : x ∈ closure A := subset_closure hx.1
    exact And.intro hx.1 (And.intro hx_cl hx.2)