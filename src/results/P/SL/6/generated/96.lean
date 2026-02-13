

theorem P1_iff_P2_and_P3_of_open_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior (A : Set X)))) :
    Topology.P1 (A : Set X) ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  constructor
  · intro hP1
    have hP2 : Topology.P2 (A : Set X) :=
      Topology.P1_and_open_closure_interior_implies_P2 (A := A) hP1 hOpen
    have hP3 : Topology.P3 (A : Set X) :=
      Topology.P1_and_open_closure_interior_implies_P3 (A := A) hP1 hOpen
    exact And.intro hP2 hP3
  · rintro ⟨hP2, _hP3⟩
    exact Topology.P2_implies_P1 (A := A) hP2