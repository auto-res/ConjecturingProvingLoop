

theorem P1_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A ↔ Topology.P3 A := by
  constructor
  · intro _hP1
    exact P3_of_open (A := A) hA
  · intro _hP3
    exact P1_of_open (A := A) hA