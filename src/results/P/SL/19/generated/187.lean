

theorem Topology.closure_interior_inter_frontier_eq_closure_interior_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ∩ frontier A =
      closure (interior A) \ interior A := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxClosInt, hxFront⟩
    exact And.intro hxClosInt hxFront.2
  · intro hx
    rcases hx with ⟨hxClosInt, hxNotInt⟩
    have hxClosA : x ∈ closure A :=
      (Topology.closure_interior_subset_closure (A := A)) hxClosInt
    exact And.intro hxClosInt ⟨hxClosA, hxNotInt⟩