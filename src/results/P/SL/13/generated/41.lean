

theorem Topology.closure_interior_closure_eq_closure_of_isOpen {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    closure (interior (closure A)) = closure A := by
  apply Set.Subset.antisymm
  ·
    have h_subset : interior (closure A) ⊆ closure A :=
      interior_subset
    have h_closure : closure (interior (closure A)) ⊆ closure (closure A) :=
      closure_mono h_subset
    simpa [closure_closure] using h_closure
  ·
    have h_interior : (A : Set X) ⊆ interior (closure A) :=
      interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hA
    have h_closure : closure (A : Set X) ⊆ closure (interior (closure A)) :=
      closure_mono h_interior
    simpa using h_closure