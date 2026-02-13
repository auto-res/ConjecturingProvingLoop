

theorem P2_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsClosed (B : Set X)) :
    P2 (X := X) (A \ B) := by
  -- `A \ B` is open because it is the difference of an open and a closed set.
  have hOpen : IsOpen ((A \ B : Set X)) :=
    IsOpen.diff (X := X) (A := A) (B := B) hA hB
  -- Every open set satisfies `P2`.
  exact isOpen_implies_P2 (X := X) (A := A \ B) hOpen