

theorem closure_eq_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 A) : closure A = closure (interior A) := by
  apply subset_antisymm
  ·
    have h₁ : A ⊆ closure (interior A) := by
      calc
        A ⊆ interior (closure (interior A)) := h
        _ ⊆ closure (interior A) := interior_subset
    have : closure A ⊆ closure (closure (interior A)) := closure_mono h₁
    simpa [closure_closure] using this
  ·
    exact closure_mono (interior_subset : interior A ⊆ A)