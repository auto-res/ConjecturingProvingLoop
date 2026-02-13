

theorem Topology.boundary_inter_subset_union_boundary
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B : Set X) \ interior (A ∩ B) ⊆
      (closure A \ interior A) ∪ (closure B \ interior B) := by
  classical
  intro x hx
  rcases hx with ⟨hx_clAB, hx_not_intAB⟩
  -- `x` lies in the closures of both `A` and `B`.
  have h_cl_subset := (Topology.closure_inter_subset (A := A) (B := B)) hx_clAB
  have hx_clA : x ∈ closure A := h_cl_subset.1
  have hx_clB : x ∈ closure B := h_cl_subset.2
  -- Express `interior (A ∩ B)` via interiors of the factors.
  have h_int_eq : interior (A ∩ B : Set X) = interior A ∩ interior B :=
    Topology.interior_inter_eq_inter (A := A) (B := B)
  -- At least one of `x ∉ interior A`, `x ∉ interior B` must hold.
  by_cases hx_intA : x ∈ interior A
  · -- Then `x ∉ interior B`, otherwise `x ∈ interior (A ∩ B)`.
    have hx_not_intB : x ∉ interior B := by
      intro hx_intB
      have : x ∈ interior (A ∩ B) := by
        -- Rewriting via `h_int_eq`.
        have : x ∈ interior A ∩ interior B := ⟨hx_intA, hx_intB⟩
        simpa [h_int_eq] using this
      exact hx_not_intAB this
    -- Hence `x` is in the boundary of `B`.
    exact Or.inr ⟨hx_clB, hx_not_intB⟩
  · -- `x` is not in `interior A`, so it lies in the boundary of `A`.
    exact Or.inl ⟨hx_clA, hx_intA⟩