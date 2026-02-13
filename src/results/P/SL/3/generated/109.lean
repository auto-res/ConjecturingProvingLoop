

theorem closure_interior_eq_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) (hP2 : Topology.P2 (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  -- A set that is both closed and satisfies `P2` is open.
  have hOpen : IsOpen (A : Set X) :=
    isOpen_of_isClosed_and_P2 (A := A) hA_closed hP2
  -- Hence `interior A = A`.
  have hInt : interior (A : Set X) = A := hOpen.interior_eq
  -- Use the facts that `closure A = A` (since `A` is closed) and `interior A = A`.
  calc
    closure (interior (A : Set X))
        = closure (A : Set X) := by
          simpa [hInt]
    _ = A := hA_closed.closure_eq