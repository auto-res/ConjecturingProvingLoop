

theorem Topology.closure_interior_closure_interior_eq_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply Set.Subset.antisymm
  ·
    have h_subset :
        interior (closure (interior A)) ⊆ closure (interior A) := by
      simpa using interior_subset
    have h_closure :
        closure (interior (closure (interior A))) ⊆
          closure (closure (interior A)) :=
      closure_mono h_subset
    simpa [closure_closure] using h_closure
  ·
    have h_open : IsOpen (interior A) := isOpen_interior
    have h_inner :
        (interior A : Set X) ⊆ interior (closure (interior A)) :=
      interior_maximal
        (subset_closure : (interior A : Set X) ⊆ closure (interior A)) h_open
    have h_closure :
        closure (interior A) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h_inner
    exact h_closure