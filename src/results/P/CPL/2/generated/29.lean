

theorem P3_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P3 (X:=X) A ↔ Topology.P2 (X:=X) A := by
  constructor
  · intro _hP3
    exact P2_of_open (X := X) (A := A) hA
  · intro hP2
    exact P3_of_P2 (A := A) hP2