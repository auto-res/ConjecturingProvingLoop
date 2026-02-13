

theorem P3_iff_isClopen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P3 A ↔ IsClopen A := by
  -- For closed sets, `P3 A` is equivalent to `IsOpen A`.
  have hOpen : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_iff_isOpen_of_isClosed (A := A) hA
  constructor
  · intro hP3
    -- From `P3` obtain openness, then combine with closedness.
    have hA_open : IsOpen A := hOpen.mp hP3
    exact ⟨hA, hA_open⟩
  · intro hClopen
    -- Openness of `A` implies `P3 A`.
    exact Topology.P3_of_isOpen (A := A) hClopen.2