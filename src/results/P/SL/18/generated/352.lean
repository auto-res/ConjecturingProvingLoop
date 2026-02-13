

theorem P2_iff_P3_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClopen : IsClopen (A : Set X)) :
    Topology.P2 A ↔ Topology.P3 A := by
  -- A clopen set is, in particular, open.
  have hOpen : IsOpen (A : Set X) := hClopen.2
  -- For open sets, `P2` and `P3` are equivalent.
  simpa using Topology.P2_iff_P3_of_open (A := A) hOpen