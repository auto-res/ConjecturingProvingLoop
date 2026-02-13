

theorem Topology.frontier_inter_eq_diff_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} : (A : Set X) ∩ frontier A = A \ interior A := by
  ext x
  constructor
  · intro hx
    have hA : x ∈ A := hx.1
    have hNotInt : x ∉ interior A := (hx.2).2
    exact And.intro hA hNotInt
  · intro hx
    have hA : x ∈ A := hx.1
    have hNotInt : x ∉ interior A := hx.2
    have hClos : x ∈ closure A := subset_closure hA
    have hFront : x ∈ frontier A := And.intro hClos hNotInt
    exact And.intro hA hFront