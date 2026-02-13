

theorem Topology.P2_iff_P1_and_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  -- `P2 A` and `P3 A` are each equivalent to `IsOpen A` for closed `A`.
  have hP2Open : Topology.P2 A ↔ IsOpen A :=
    Topology.P2_closed_iff_isOpen (A := A) hA
  have hP3Open : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_closed_iff_isOpen (A := A) hA
  constructor
  · intro hP2
    -- From `P2` obtain openness, hence `P1` and `P3`.
    have hOpen : IsOpen A := (hP2Open).1 hP2
    have hP1 : Topology.P1 A := Topology.IsOpen_P1 (A := A) hOpen
    have hP3 : Topology.P3 A := (hP3Open).2 hOpen
    exact ⟨hP1, hP3⟩
  · rintro ⟨_, hP3⟩
    -- From `P3` recover openness, hence `P2`.
    have hOpen : IsOpen A := (hP3Open).1 hP3
    exact (hP2Open).2 hOpen