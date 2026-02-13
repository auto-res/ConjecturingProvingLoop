

theorem closure_eq_closure_interior_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    closure A = closure (interior (closure A)) := by
  apply Set.Subset.antisymm
  ·
    -- `A ⊆ closure (interior (closure A))` by `P1`.
    have hSub : (A : Set X) ⊆ closure (interior (closure A)) :=
      Topology.subset_closure_interior_closure_of_P1 hP1
    -- Taking closures gives the required inclusion.
    have hClos : closure A ⊆ closure (closure (interior (closure A))) :=
      closure_mono hSub
    simpa [closure_closure] using hClos
  ·
    exact Topology.closure_interior_closure_subset_closure (A := A)