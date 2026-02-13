

theorem Topology.P3_iff_P1_and_P2_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P3 A ↔ (Topology.P1 A ∧ Topology.P2 A) := by
  -- `P3 A` and `P2 A` are each equivalent to `IsOpen A` whenever `A` is closed.
  have hP3Open : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_closed_iff_isOpen (A := A) hA
  have hP2Open : Topology.P2 A ↔ IsOpen A :=
    Topology.P2_closed_iff_isOpen (A := A) hA
  constructor
  · intro hP3
    -- From `P3` obtain openness, then derive `P1` and `P2`.
    have hOpen : IsOpen A := (hP3Open).1 hP3
    have hP1 : Topology.P1 A := Topology.IsOpen_P1 (A := A) hOpen
    have hP2 : Topology.P2 A := (IsOpen_P2 (A := A) hOpen)
    exact ⟨hP1, hP2⟩
  · rintro ⟨_, hP2⟩
    -- From `P2` recover openness, then obtain `P3`.
    have hOpen : IsOpen A := (hP2Open).1 hP2
    exact (hP3Open).2 hOpen