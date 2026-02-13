

theorem Topology.boundary_union_subset_union_boundary {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∪ B) \ interior (A ∪ B) ⊆
      (closure A \ interior A) ∪ (closure B \ interior B) := by
  intro x hx
  rcases hx with ⟨hx_cl_union, hx_not_int_union⟩
  -- From `x ∈ closure (A ∪ B)` deduce `x ∈ closure A ∪ closure B`.
  have hx_closure_union : x ∈ closure A ∪ closure B := by
    have h_eq := (Topology.closure_union_eq (A) (B))
    have : x ∈ closure (A ∪ B) := hx_cl_union
    simpa [h_eq] using this
  -- `x` is not in `interior A` (otherwise it would be in `interior (A ∪ B)`).
  have h_not_intA : x ∉ interior A := by
    intro hx_intA
    have h_subset : interior A ⊆ interior (A ∪ B) := by
      have h_sub : (A : Set X) ⊆ A ∪ B := by
        intro y hy; exact Or.inl hy
      exact interior_mono h_sub
    exact hx_not_int_union (h_subset hx_intA)
  -- Likewise, `x` is not in `interior B`.
  have h_not_intB : x ∉ interior B := by
    intro hx_intB
    have h_subset : interior B ⊆ interior (A ∪ B) := by
      have h_sub : (B : Set X) ⊆ A ∪ B := by
        intro y hy; exact Or.inr hy
      exact interior_mono h_sub
    exact hx_not_int_union (h_subset hx_intB)
  -- Finish by cases on membership in `closure A ∪ closure B`.
  cases hx_closure_union with
  | inl hx_clA =>
      exact Or.inl ⟨hx_clA, h_not_intA⟩
  | inr hx_clB =>
      exact Or.inr ⟨hx_clB, h_not_intB⟩