

theorem P1_iff_P2_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClopen : IsClopen (A : Set X)) :
    Topology.P1 A ↔ Topology.P2 A := by
  have hOpen : IsOpen (A : Set X) := hClopen.2
  simpa using Topology.P1_iff_P2_of_open (A := A) hOpen