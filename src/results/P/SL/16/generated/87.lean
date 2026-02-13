

theorem Topology.interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure A))) = interior (closure A) := by
  apply subset_antisymm
  · -- `interior (closure (interior (closure A))) ⊆ interior (closure A)`
    have h₁ : closure (interior (closure A)) ⊆ closure A := by
      have h_inner : interior (closure A) ⊆ closure A := interior_subset
      have : closure (interior (closure A)) ⊆ closure (closure A) :=
        closure_mono h_inner
      simpa [closure_closure] using this
    exact interior_mono h₁
  · -- `interior (closure A) ⊆ interior (closure (interior (closure A)))`
    have h₂ : interior (closure A) ⊆ closure (interior (closure A)) := by
      intro x hx
      exact subset_closure hx
    have h_open : IsOpen (interior (closure A)) := isOpen_interior
    exact interior_maximal h₂ h_open