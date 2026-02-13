

theorem P2_closed_iff_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ IsOpen A := by
  -- `P3` and openness are equivalent for closed sets
  have hP3_iff_open : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_closed_iff_open hA_closed
  constructor
  · intro hP2
    -- `P2` ⇒ `P3` ⇒ `IsOpen`
    have hP3 : Topology.P3 A := Topology.P2_implies_P3 hP2
    exact (hP3_iff_open).1 hP3
  · intro hOpen
    -- `IsOpen` ⇒ `P2`
    exact Topology.P2_of_open hOpen