

theorem Topology.boundaryClosure_subset_boundary {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A : Set X) \ interior (closure A) ⊆ closure A \ interior A := by
  intro x hx
  rcases hx with ⟨hx_cl, hx_not_int_cl⟩
  have hx_not_intA : x ∉ interior (A : Set X) := by
    intro hx_intA
    have h_subset : interior (A : Set X) ⊆ interior (closure A) :=
      Topology.interior_subset_interiorClosure (A := A)
    have : x ∈ interior (closure A) := h_subset hx_intA
    exact hx_not_int_cl this
  exact ⟨hx_cl, hx_not_intA⟩