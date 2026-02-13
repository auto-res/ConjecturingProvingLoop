

theorem P3_implies_P1_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 A → Topology.P1 A := by
  intro hP3
  -- From `P3` and closedness of `A`, deduce that `A` is open.
  have hOpen : IsOpen A :=
    (Topology.P3_closed_iff_open hA_closed).1 hP3
  -- For an open set, the interior coincides with the set itself.
  have hInt : interior A = A := hOpen.interior_eq
  -- Unfold the definition of `P1` and prove the required inclusion.
  dsimp [Topology.P1]
  intro x hxA
  -- View `x` as an element of `interior A` using `hInt`.
  have hxInt : x ∈ interior A := by
    simpa [hInt] using hxA
  -- Any point of `interior A` lies in `closure (interior A)`.
  exact subset_closure hxInt