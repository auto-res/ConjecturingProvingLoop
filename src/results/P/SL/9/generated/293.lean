

theorem Topology.frontier_inter_subset_frontier_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∩ B : Set X) ⊆
      (frontier A ∩ closure B) ∪ (frontier B ∩ closure A) := by
  intro x hx
  rcases hx with ⟨hx_clAB, hx_not_intAB⟩
  -- From the closure of an intersection to the intersection of the closures.
  have h_cl_subset :
      closure (A ∩ B : Set X) ⊆ closure A ∩ closure B :=
    Topology.closure_inter_subset (A := A) (B := B)
  have hx_clA : x ∈ closure A := (h_cl_subset hx_clAB).1
  have hx_clB : x ∈ closure B := (h_cl_subset hx_clAB).2
  -- Express the interior of an intersection.
  have h_int_eq :
      interior (A ∩ B : Set X) = interior A ∩ interior B :=
    Topology.interior_inter_eq_inter (A := A) (B := B)
  -- Case analysis on membership in `interior A`.
  by_cases hIntA : x ∈ interior A
  · -- Then `x ∉ interior B`, otherwise `x` would be in `interior (A ∩ B)`.
    have h_not_intB : x ∉ interior B := by
      intro hIntB
      have : x ∈ interior (A ∩ B : Set X) := by
        have : x ∈ interior A ∩ interior B := ⟨hIntA, hIntB⟩
        simpa [h_int_eq] using this
      exact hx_not_intAB this
    -- Assemble membership in `frontier B ∩ closure A`.
    have hx_frontierB : x ∈ frontier B := ⟨hx_clB, h_not_intB⟩
    exact Or.inr ⟨hx_frontierB, hx_clA⟩
  · -- Otherwise, `x ∉ interior A`, so `x` is in `frontier A ∩ closure B`.
    have h_not_intA : x ∉ interior A := hIntA
    have hx_frontierA : x ∈ frontier A := ⟨hx_clA, h_not_intA⟩
    exact Or.inl ⟨hx_frontierA, hx_clB⟩