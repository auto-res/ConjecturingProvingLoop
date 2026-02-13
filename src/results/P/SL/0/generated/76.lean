

theorem interior_closure_eq_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) =
      interior (closure (interior (closure (A : Set X)))) := by
  -- First inclusion: `interior (closure A) ⊆ interior (closure (interior (closure A)))`.
  have h₁ :
      (interior (closure (A : Set X)) : Set X) ⊆
        closure (interior (closure (A : Set X))) := subset_closure
  have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  have h_left :
      (interior (closure (A : Set X)) : Set X) ⊆
        interior (closure (interior (closure (A : Set X)))) :=
    interior_maximal h₁ hOpen
  -- Second inclusion: `interior (closure (interior (closure A))) ⊆ interior (closure A)`.
  have h_right :
      (interior (closure (interior (closure (A : Set X)))) : Set X) ⊆
        interior (closure (A : Set X)) := by
    -- This is an instance of the monotonicity lemma with `A := closure A`.
    simpa [closure_closure] using
      (Topology.interior_closure_interior_subset_interior_closure
        (X := X) (A := closure (A : Set X)))
  exact Set.Subset.antisymm h_left h_right