

theorem Topology.interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (A : Set X)))) =
      interior (closure (A : Set X)) := by
  apply subset_antisymm
  ·
    have hsubset :
        closure (interior (closure (A : Set X))) ⊆ closure (A : Set X) :=
      Topology.closure_interior_closure_subset_closure (A := A)
    exact interior_mono hsubset
  ·
    have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    have hsubset :
        (interior (closure (A : Set X)) : Set X) ⊆
          closure (interior (closure (A : Set X))) := by
      intro x hx
      exact subset_closure hx
    have hsubset' :
        (interior (closure (A : Set X)) : Set X) ⊆
          interior (closure (interior (closure (A : Set X)))) :=
      interior_maximal hsubset hOpen
    exact hsubset'