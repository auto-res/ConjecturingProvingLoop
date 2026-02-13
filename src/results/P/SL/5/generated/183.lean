

theorem P1_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsClosed (B : Set X)) :
    Topology.P1 (X := X) (A \ B) := by
  -- `A \ B` is open because it is the difference of an open set and a closed set.
  have hOpen : IsOpen ((A \ B) : Set X) :=
    IsOpen.diff (X := X) (A := A) (B := B) hA hB
  -- Every open set satisfies `P1`.
  exact Topology.isOpen_implies_P1 (X := X) (A := A \ B) hOpen