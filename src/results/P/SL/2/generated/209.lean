

theorem Topology.interior_eq_self_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = (A : Set X) → Topology.P1 A := by
  intro hIntEq
  -- From `interior A = A`, we deduce that `A` is open.
  have hOpen : IsOpen (A : Set X) :=
    (isOpen_iff_interior_eq (A := A)).2 hIntEq
  -- Every open set satisfies `P1`.
  exact Topology.isOpen_implies_P1 (A := A) hOpen