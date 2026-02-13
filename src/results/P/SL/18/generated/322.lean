

theorem clopen_of_closed_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP3 : Topology.P3 A) :
    IsClopen (A : Set X) := by
  -- From `P3` and the closedness of `A`, we deduce that `A` is open.
  have hOpen : IsOpen (A : Set X) :=
    (Topology.P3_closed_iff_open (A := A) hClosed).1 hP3
  -- Combine the closedness and openness to obtain that `A` is clopen.
  exact ⟨hClosed, hOpen⟩