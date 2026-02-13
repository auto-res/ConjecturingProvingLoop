

theorem P2_implies_P1_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP2 : P2 (X := X) A) :
    P1 (X := X) A := by
  -- From the assumptions, `A` is both closed and satisfies `P2`. 
  -- The existing result `isOpen_of_isClosed_and_P2` tells us that `A` is open.
  have hOpen : IsOpen A :=
    isOpen_of_isClosed_and_P2 (X := X) (A := A) hClosed hP2
  -- Any open set satisfies `P1` by `isOpen_implies_P1`.
  exact isOpen_implies_P1 (X := X) (A := A) hOpen