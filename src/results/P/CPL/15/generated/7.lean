

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (closure (interior A)) := by
  intro x hx
  have h_subset :
      (closure (interior A) : Set X) ⊆
        closure (interior (closure (interior A))) := by
    -- First, show `interior A ⊆ interior (closure (interior A))`
    have h_inner :
        (interior A : Set X) ⊆ interior (closure (interior A)) := by
      exact interior_maximal
        (subset_closure :
          (interior A : Set X) ⊆ closure (interior A))
        isOpen_interior
    -- Then, take closures on both sides
    exact closure_mono h_inner
  exact h_subset hx

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h_dense : closure A = Set.univ) : P3 A := by
  intro x hx
  simpa [h_dense, interior_univ] using (Set.mem_univ x)