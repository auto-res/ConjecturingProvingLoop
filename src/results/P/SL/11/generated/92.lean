

theorem interior_closure_interior_closure_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure A))) = interior (closure A) := by
  apply subset_antisymm
  ·
    -- First inclusion: use the existing general monotonicity lemma.
    simpa using
      (interior_closure_interior_subset (A := closure A))
  ·
    -- Second inclusion: use `interior_maximal` with openness of `interior (closure A)`.
    have hsubset : interior (closure A) ⊆ closure (interior (closure A)) :=
      (subset_closure : (interior (closure A) : Set X) ⊆ closure (interior (closure A)))
    have hOpen : IsOpen (interior (closure A)) := isOpen_interior
    exact interior_maximal hsubset hOpen