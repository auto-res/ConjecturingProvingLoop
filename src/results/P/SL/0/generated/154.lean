

theorem interior_closure_subset_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ⊆
      interior (closure (interior (closure (A : Set X)))) := by
  -- The set `interior (closure A)` is open.
  have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  -- And it is contained in `closure (interior (closure A))`.
  have hSub :
      (interior (closure (A : Set X)) : Set X) ⊆
        closure (interior (closure (A : Set X))) :=
    subset_closure
  -- Apply the maximality property of `interior`.
  exact interior_maximal hSub hOpen