

theorem Topology.boundaryInterior_subset_boundary {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (closure (interior (A : Set X)) \ interior A) ⊆
      closure (A : Set X) \ interior A := by
  intro x hx
  rcases hx with ⟨hx_cl, hx_not_int⟩
  -- Since `interior A ⊆ A`, taking closures yields
  -- `closure (interior A) ⊆ closure A`.
  have h_subset :
      closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  -- Transport `x ∈ closure (interior A)` along this inclusion.
  have hx_clA : (x : X) ∈ closure (A : Set X) := h_subset hx_cl
  exact ⟨hx_clA, hx_not_int⟩