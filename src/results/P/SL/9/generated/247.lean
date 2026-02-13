

theorem Topology.frontier_inter_subset_union_frontier {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    frontier (A ∩ B : Set X) ⊆ frontier A ∪ frontier B := by
  classical
  intro x hx
  -- Decompose `hx` into closure and non‐interior parts.
  have hx_cl : x ∈ closure (A ∩ B : Set X) := hx.1
  have hx_not_int : x ∉ interior (A ∩ B : Set X) := hx.2
  -- `closure (A ∩ B)` is contained in `closure A ∩ closure B`.
  have h_cl_subset :
      closure (A ∩ B : Set X) ⊆ closure A ∩ closure B :=
    Topology.closure_inter_subset (A := A) (B := B)
  have hx_clA : x ∈ closure A := (h_cl_subset hx_cl).1
  have hx_clB : x ∈ closure B := (h_cl_subset hx_cl).2
  -- Rewrite `interior (A ∩ B)` using interiors of the factors.
  have h_int_eq :
      interior (A ∩ B : Set X) = interior A ∩ interior B :=
    Topology.interior_inter_eq_inter (A := A) (B := B)
  have hx_not_intAB : x ∉ interior A ∩ interior B := by
    have : x ∉ interior (A ∩ B : Set X) := hx_not_int
    simpa [h_int_eq] using this
  by_cases hx_intA : x ∈ interior A
  · -- Then `x ∉ interior B`, so `x ∈ frontier B`.
    have hx_not_intB : x ∉ interior B := by
      intro hx_intB
      have : x ∈ interior A ∩ interior B := ⟨hx_intA, hx_intB⟩
      exact hx_not_intAB this
    have hx_frontierB : x ∈ frontier B := ⟨hx_clB, hx_not_intB⟩
    exact Or.inr hx_frontierB
  · -- Otherwise `x ∈ frontier A`.
    have hx_frontierA : x ∈ frontier A := ⟨hx_clA, hx_intA⟩
    exact Or.inl hx_frontierA