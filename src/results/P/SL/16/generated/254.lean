

theorem Topology.closure_interior_closure_interior_eq_closure_interior_simple
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply subset_antisymm
  · -- `closure (interior (closure (interior A))) ⊆ closure (interior A)`
    have : closure (interior (closure (interior A))) ⊆
        closure (interior A) := by
      -- This is an instance of `closure (interior (closure B)) ⊆ closure B`
      -- with `B = interior A`.
      simpa using
        (Topology.closure_interior_closure_subset_closure
          (X := X) (A := interior A))
    exact this
  · -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`
    have : interior A ⊆ interior (closure (interior A)) :=
      Topology.interior_subset_interior_closure_interior
        (X := X) (A := A)
    exact closure_mono this