

theorem closure_eq_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : P2 A) : closure A = closure (interior A) := by
  apply le_antisymm
  ·
    have hA : (A : Set X) ⊆ closure (interior A) := by
      have hAi : (A : Set X) ⊆ interior (closure (interior A)) := h
      exact hAi.trans interior_subset
    simpa [closure_closure] using (closure_mono hA)
  ·
    have : (interior A : Set X) ⊆ A := interior_subset
    simpa using (closure_mono this)