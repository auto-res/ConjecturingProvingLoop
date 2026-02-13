

theorem Topology.interior_closure_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure A))) = interior (closure A) := by
  apply subset_antisymm
  ·
    -- `LHS ⊆ RHS`
    have h₁ : closure (interior (closure A)) ⊆ closure A := by
      have : interior (closure A) ⊆ closure A := interior_subset
      have h := closure_mono this
      simpa [closure_closure] using h
    have : interior (closure (interior (closure A))) ⊆ interior (closure A) :=
      interior_mono h₁
    exact this
  ·
    -- `RHS ⊆ LHS`
    have h_subset : interior (closure A) ⊆ closure (interior (closure A)) :=
      subset_closure
    have h_isOpen : IsOpen (interior (closure A)) := isOpen_interior
    have : interior (closure A) ⊆ interior (closure (interior (closure A))) :=
      interior_maximal h_subset h_isOpen
    exact this