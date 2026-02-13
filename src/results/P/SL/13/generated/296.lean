

theorem Topology.closure_eq_closureInterior_union_boundary {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) =
      closure (interior A) ∪ (closure (A : Set X) \ interior A) := by
  -- We establish both inclusions and then apply `Subset.antisymm`.
  apply Set.Subset.antisymm
  · -- `closure A ⊆ …`
    intro x hx_clA
    by_cases hx_int : (x : X) ∈ interior A
    · -- If `x ∈ interior A`, then `x ∈ closure (interior A)`.
      have : (x : X) ∈ closure (interior A) := subset_closure hx_int
      exact Or.inl this
    · -- Otherwise `x ∈ closure A \ interior A`.
      exact Or.inr ⟨hx_clA, hx_int⟩
  · -- The reverse inclusion is straightforward since both summands lie in `closure A`.
    intro x hx
    cases hx with
    | inl hx_clIntA =>
        -- `closure (interior A) ⊆ closure A`
        exact (closure_mono (interior_subset : interior A ⊆ A)) hx_clIntA
    | inr hx_boundary =>
        -- The boundary is defined using `closure A`.
        exact hx_boundary.1