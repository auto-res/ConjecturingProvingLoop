

theorem interior_closure_eq_self_of_P2_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) →
      interior (closure (A : Set X)) = closure A := by
  intro hP2
  -- From `P2` we know that `closure A` is open.
  have hOpen : IsOpen (closure (A : Set X)) :=
    Topology.open_of_P2_closure (A := A) hP2
  -- For an open set, its interior equals itself.
  simpa using hOpen.interior_eq