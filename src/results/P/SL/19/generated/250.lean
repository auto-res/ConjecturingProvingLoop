

theorem Topology.frontier_inter_subset_frontier_inter_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∩ B) ⊆
      (frontier A ∩ closure B) ∪ (frontier B ∩ closure A) := by
  intro x hx
  -- Decompose the hypothesis `hx`.
  rcases hx with ⟨hxClosInter, hxNotIntInter⟩
  -- Membership in the individual closures.
  have hxClosA : x ∈ closure A := by
    have hSub : (A ∩ B : Set X) ⊆ A := fun y hy => hy.1
    exact (closure_mono hSub) hxClosInter
  have hxClosB : x ∈ closure B := by
    have hSub : (A ∩ B : Set X) ⊆ B := fun y hy => hy.2
    exact (closure_mono hSub) hxClosInter
  -- Case distinction on `x ∈ interior A`.
  by_cases hIntA : x ∈ interior A
  · -- If `x ∈ interior A`, then `x ∉ interior B`.
    have hNotIntB : x ∉ interior B := by
      intro hIntB
      -- `x` would then lie in `interior (A ∩ B)`, contradicting `hxNotIntInter`.
      have hSub : (interior A ∩ interior B : Set X) ⊆ A ∩ B := by
        intro y hy; exact ⟨interior_subset hy.1, interior_subset hy.2⟩
      have hOpen : IsOpen (interior A ∩ interior B) :=
        isOpen_interior.inter isOpen_interior
      have hInc : (interior A ∩ interior B : Set X) ⊆ interior (A ∩ B) :=
        interior_maximal hSub hOpen
      have : x ∈ interior (A ∩ B) := hInc ⟨hIntA, hIntB⟩
      exact hxNotIntInter this
    -- Assemble membership in `frontier B ∩ closure A`.
    have hFrontB : x ∈ frontier B := And.intro hxClosB hNotIntB
    exact Or.inr ⟨hFrontB, hxClosA⟩
  · -- Otherwise `x ∉ interior A`, so `x ∈ frontier A`.
    have hFrontA : x ∈ frontier A := And.intro hxClosA hIntA
    exact Or.inl ⟨hFrontA, hxClosB⟩