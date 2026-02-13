

theorem eq_empty_of_P2_and_empty_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = (∅ : Set X) → Topology.P2 A → A = (∅ : Set X) := by
  intro hInt hP2
  -- `P2` gives an inclusion of `A` into an interior of a closure.
  have h_sub : (A : Set X) ⊆ interior (closure (interior A)) := hP2
  -- Simplify the target interior using the assumption `interior A = ∅`.
  have h_empty : interior (closure (interior A)) = (∅ : Set X) := by
    simpa [hInt, closure_empty, interior_empty]
  -- From the two facts we get `A ⊆ ∅`.
  have h_subset_empty : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hx
    have : x ∈ interior (closure (interior A)) := h_sub hx
    simpa [h_empty] using this
  -- Conclude the desired equality by extensionality.
  apply subset_antisymm h_subset_empty (Set.empty_subset _)