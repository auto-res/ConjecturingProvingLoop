

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (closure (interior A)) := by
  intro x hx
  -- We exhibit the required inclusion between the two closures.
  have h_subset :
      closure (interior A) ⊆
        closure (interior (closure (interior A))) := by
    -- First, show the inclusion for the interiors.
    have h_int :
        interior A ⊆ interior (closure (interior A)) := by
      apply interior_maximal
      · exact subset_closure
      · exact isOpen_interior
    -- Take closures on both sides.
    exact closure_mono h_int
  -- Apply the inclusion to the given point.
  exact h_subset hx