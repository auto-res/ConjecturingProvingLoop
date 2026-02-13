

theorem Topology.interior_subset_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure (interior (closure A))) := by
  intro x hx
  -- First inclusion: `interior A ⊆ interior (closure A)`
  have h₁ : (interior A : Set X) ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (A := A)
  have hx₁ : x ∈ interior (closure A) := h₁ hx
  -- Second inclusion:
  -- `interior (closure A) ⊆ interior (closure (interior (closure A)))`
  have h₂ :
      (interior (closure A) : Set X) ⊆
        interior (closure (interior (closure A))) := by
    -- This follows from the same lemma applied to `interior (closure A)`
    have h :=
      Topology.interior_subset_interior_closure
        (A := interior (closure A))
    simpa [interior_interior] using h
  exact h₂ hx₁