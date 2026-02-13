

theorem Topology.interior_closure_subset_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ⊆
      interior (closure (interior (closure A))) := by
  -- `interior (closure A)` is open.
  have h_open : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  -- And it is contained in `closure (interior (closure A))`.
  have h_subset :
      (interior (closure (A : Set X)) : Set X) ⊆
        closure (interior (closure (A : Set X))) :=
    subset_closure
  -- Apply the maximality property of the interior for an open set.
  exact interior_maximal h_subset h_open