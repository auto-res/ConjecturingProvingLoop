

theorem Topology.interior_closure_subset_closure_interior_union_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ⊆ closure (interior A) ∪ frontier A := by
  intro x hxInt
  by_cases h : x ∈ closure (interior A)
  · exact Or.inl h
  ·
    -- If `x ∉ closure (interior A)`, then it lies in the set difference
    have hxDiff : x ∈ interior (closure A) \ closure (interior A) :=
      And.intro hxInt h
    -- The previously proved lemma sends this difference into the frontier
    have hxFront :
        x ∈ frontier A :=
      (Topology.interior_closure_diff_closure_interior_subset_frontier
        (A := A)) hxDiff
    exact Or.inr hxFront