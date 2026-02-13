

theorem Topology.interior_closure_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    interior (closure (⋂ i, A i)) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  have hx_i : ∀ i, x ∈ interior (closure (A i)) := by
    intro i
    -- Establish the monotone relationships needed to transfer `hx`.
    have h_subset₁ : (⋂ j, A j) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    have h_subset₂ : closure (⋂ j, A j) ⊆ closure (A i) :=
      closure_mono h_subset₁
    have h_subset₃ : interior (closure (⋂ j, A j)) ⊆ interior (closure (A i)) :=
      interior_mono h_subset₂
    exact h_subset₃ hx
  exact Set.mem_iInter.2 hx_i