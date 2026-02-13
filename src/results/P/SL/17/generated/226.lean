

theorem Topology.interior_closure_union_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∪ B)) = interior (closure A ∪ closure B) := by
  -- Since `closure` distributes over unions, rewrite and finish.
  have h : closure (A ∪ B) = closure A ∪ closure B := by
    simpa using closure_union (s := A) (t := B)
  simpa using congrArg interior h