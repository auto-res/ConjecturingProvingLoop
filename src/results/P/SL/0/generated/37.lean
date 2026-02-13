

theorem interior_closure_interior_idempotent {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  -- First inclusion: left ⊆ right.
  have h₁ :
      interior (closure (interior (closure (interior A)))) ⊆
        interior (closure (interior A)) := by
    simpa [closure_closure] using
      (Topology.interior_closure_interior_subset_interior_closure
        (X := X) (A := closure (interior A)))
  -- Second inclusion: right ⊆ left.
  have h₂ :
      interior (closure (interior A)) ⊆
        interior (closure (interior (closure (interior A)))) := by
    have hSub :
        (interior (closure (interior A)) : Set X) ⊆
          closure (interior (closure (interior A))) := subset_closure
    have hOpen : IsOpen (interior (closure (interior A)) : Set X) :=
      isOpen_interior
    exact interior_maximal hSub hOpen
  exact subset_antisymm h₁ h₂