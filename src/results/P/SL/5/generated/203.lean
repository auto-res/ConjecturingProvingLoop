

theorem P3_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsClosed (B : Set X)) :
    Topology.P3 (X := X) (A \ B) := by
  -- The difference of an open set and a closed set is open.
  have hOpen : IsOpen ((A \ B) : Set X) :=
    IsOpen.diff (X := X) (A := A) (B := B) hA hB
  -- Every open set satisfies `P3`.
  exact Topology.isOpen_implies_P3 (X := X) (A := A \ B) hOpen