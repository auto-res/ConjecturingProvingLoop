

theorem Topology.boundaryInterior_subset_boundary
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) \ interior A ⊆ closure A \ interior A := by
  intro x hx
  have hx_closureInt : x ∈ closure (interior A) := hx.1
  have hx_not_int : x ∉ interior A := hx.2
  have h_subset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  have hx_closureA : x ∈ closure A := h_subset hx_closureInt
  exact ⟨hx_closureA, hx_not_int⟩