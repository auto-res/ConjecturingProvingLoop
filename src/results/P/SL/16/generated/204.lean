

theorem Topology.closure_interior_union_subset_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∪ B)) ⊆ closure A ∪ closure B := by
  intro x hx
  -- `interior (A ∪ B)` is contained in `A ∪ B`.
  have h_subset : (interior (A ∪ B) : Set X) ⊆ A ∪ B := interior_subset
  -- Taking closures preserves inclusions.
  have h_closure_subset :
      closure (interior (A ∪ B)) ⊆ closure (A ∪ B) :=
    closure_mono h_subset
  -- Transport the membership of `x`.
  have hx_closure : x ∈ closure (A ∪ B) := h_closure_subset hx
  -- Rewriting the right‐hand side using `closure_union`.
  simpa [closure_union] using hx_closure