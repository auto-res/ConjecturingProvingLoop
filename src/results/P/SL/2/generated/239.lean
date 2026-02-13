

theorem Topology.isOpen_closure_implies_frontier_closure_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) →
      frontier (closure (A : Set X)) = (∅ : Set X) := by
  intro hOpen
  have hInt : interior (closure (A : Set X)) = closure (A : Set X) :=
    hOpen.interior_eq
  simp [frontier, hInt, closure_closure, Set.diff_self]