

theorem Topology.closure_interior_inter_subset {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    closure (interior A ∩ B) ⊆ closure (A ∩ B) := by
  -- `interior A` is contained in `A`, hence their intersection with `B`
  -- sits inside `A ∩ B`.
  have h_subset : (interior A ∩ B : Set X) ⊆ A ∩ B := by
    intro x hx
    exact ⟨interior_subset hx.1, hx.2⟩
  -- Taking closures preserves this inclusion.
  exact closure_mono h_subset