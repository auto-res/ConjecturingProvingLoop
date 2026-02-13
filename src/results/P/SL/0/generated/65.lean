

theorem closure_interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (A : Set X)))) =
      closure (interior (A : Set X)) := by
  apply subset_antisymm
  · -- Left ⊆ right.
    have h :
        interior (closure (interior (A : Set X))) ⊆
          closure (interior (A : Set X)) := interior_subset
    have h' := closure_mono h
    simpa [closure_closure] using h'
  · -- Right ⊆ left, using the monotonicity lemma with `A := interior A`.
    have h :=
      Topology.closure_interior_subset_closure_interior_closure
        (X := X) (A := interior (A : Set X))
    simpa [interior_interior] using h