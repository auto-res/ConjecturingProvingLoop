

theorem Topology.frontier_inter_subset_union_frontier
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∩ B) ⊆ frontier A ∪ frontier B := by
  intro x hx
  -- Decompose the hypothesis `hx : x ∈ frontier (A ∩ B)`
  rcases hx with ⟨hClAB, hNotIntAB⟩
  -- `x` is in the closures of both `A` and `B`
  have hClA : x ∈ closure A :=
    (Topology.closure_inter_subset_inter_closure
        (A := A) (B := B)) hClAB |>.1
  have hClB : x ∈ closure B :=
    (Topology.closure_inter_subset_inter_closure
        (A := A) (B := B)) hClAB |>.2
  -- Case distinction on whether `x ∈ interior A`
  by_cases hIntA : x ∈ interior A
  · -- If `x ∈ interior A`, show that `x ∈ frontier B`
    have hNotIntB : x ∉ interior B := by
      intro hIntB
      -- `x` would then lie in `interior (A ∩ B)`, contradicting `hNotIntAB`
      have hOpen : IsOpen (interior A ∩ interior B) :=
        isOpen_interior.inter isOpen_interior
      have hSub : (interior A ∩ interior B) ⊆ (A ∩ B) := by
        intro y hy
        exact ⟨interior_subset hy.1, interior_subset hy.2⟩
      have hIntSub :
          (interior A ∩ interior B) ⊆ interior (A ∩ B) :=
        interior_maximal hSub hOpen
      have : x ∈ interior (A ∩ B) := hIntSub ⟨hIntA, hIntB⟩
      exact hNotIntAB this
    -- Assemble the frontier membership for `B`
    have hFrontB : x ∈ frontier B := And.intro hClB hNotIntB
    exact Or.inr hFrontB
  · -- If `x ∉ interior A`, then `x ∈ frontier A`
    have hNotIntA : x ∉ interior A := hIntA
    have hFrontA : x ∈ frontier A := And.intro hClA hNotIntA
    exact Or.inl hFrontA