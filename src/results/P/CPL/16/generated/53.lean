

theorem open_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P3 A → IsOpen A := by
  intro hClosed hP3
  -- obtain `P2 A` from `P3 A` since `A` is closed
  have hP2 : P2 A := ((P2_iff_P3_of_closed (A := A) hClosed).2) hP3
  -- use the previous result for `P2` on closed sets
  exact open_of_P2_closed (A := A) hClosed hP2

theorem P3_of_dense_interior_closure' {X : Type*} [TopologicalSpace X] {A : Set X} : interior (closure A) = Set.univ → P3 A := by
  intro hInt
  intro x hxA
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [hInt] using this