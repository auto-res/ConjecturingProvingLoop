

theorem Topology.interior_closure_inter_frontier_eq_interior_closure_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ∩ frontier A =
      interior (closure A) \ interior A := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxIntClos, hxFront⟩
    exact ⟨hxIntClos, hxFront.2⟩
  · intro hx
    rcases hx with ⟨hxIntClos, hxNotIntA⟩
    have hxClosA : x ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hxIntClos
    have hxFront : x ∈ frontier A := And.intro hxClosA hxNotIntA
    exact And.intro hxIntClos hxFront