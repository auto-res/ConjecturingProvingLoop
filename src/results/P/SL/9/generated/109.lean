

theorem Topology.closure_inter_subset {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    closure (A ∩ B) ⊆ closure A ∩ closure B := by
  intro x hx
  have hxA : x ∈ closure A := by
    -- `A ∩ B ⊆ A`, hence their closures satisfy the same inclusion.
    have h_subset : (A ∩ B : Set X) ⊆ A := by
      intro y hy; exact hy.1
    have h_closure := closure_mono h_subset
    exact h_closure hx
  have hxB : x ∈ closure B := by
    -- Symmetric argument for `B`.
    have h_subset : (A ∩ B : Set X) ⊆ B := by
      intro y hy; exact hy.2
    have h_closure := closure_mono h_subset
    exact h_closure hx
  exact ⟨hxA, hxB⟩