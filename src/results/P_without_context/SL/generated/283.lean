

theorem interior_subset_interior_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior A ⊆ interior (closure (interior A)) := by
  -- `interior A` is open
  have h_open : IsOpen (interior A) := isOpen_interior
  -- `interior A` is contained in its closure
  have h_subset : interior A ⊆ closure (interior A) := by
    intro x hx
    exact subset_closure hx
  -- therefore, by maximality of the interior, we obtain the desired inclusion
  exact interior_maximal h_subset h_open