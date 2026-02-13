

theorem Topology.closure_inter_interior_subset {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    closure (A ∩ interior B) ⊆ closure (A ∩ B) := by
  -- Since `interior B ⊆ B`, the intersection with `A` is contained accordingly.
  have h_subset : (A ∩ interior B : Set X) ⊆ A ∩ B := by
    intro x hx
    exact ⟨hx.1, interior_subset hx.2⟩
  -- Taking closures preserves inclusions.
  exact closure_mono h_subset