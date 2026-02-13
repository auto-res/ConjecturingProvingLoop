

theorem interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (A : Set X)))) =
      interior (closure (A : Set X)) := by
  apply Set.Subset.antisymm
  ·
    have h :
        interior (closure (interior (closure (A : Set X))))
          ⊆ interior (closure (closure (A : Set X))) :=
      (Topology.interior_closure_interior_subset_interior_closure
        (A := closure (A : Set X)))
    simpa [closure_closure] using h
  ·
    have hSub :
        interior (closure (A : Set X))
          ⊆ closure (interior (closure (A : Set X))) :=
      (subset_closure :
        interior (closure (A : Set X)) ⊆
          closure (interior (closure (A : Set X))))
    have h :
        interior (interior (closure (A : Set X)))
          ⊆ interior (closure (interior (closure (A : Set X)))) :=
      interior_mono hSub
    simpa [interior_interior] using h