

theorem Topology.interior_closure_subset_self_union_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ⊆ A ∪ frontier A := by
  intro x hx
  -- First, use the existing inclusion into `interior A ∪ frontier A`.
  have h : x ∈ interior A ∪ frontier A :=
    (Topology.interior_closure_subset_interior_union_frontier (A := A)) hx
  -- Upgrade the membership from `interior A` to `A` when necessary.
  cases h with
  | inl hInt =>
      exact Or.inl (interior_subset hInt)
  | inr hFront =>
      exact Or.inr hFront