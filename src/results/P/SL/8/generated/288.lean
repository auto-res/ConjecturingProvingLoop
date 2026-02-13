

theorem P2_nonempty_iff_closureInterior_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) :
    A.Nonempty ↔ (closure (interior A)).Nonempty := by
  constructor
  · intro hA
    exact
      Topology.P2_nonempty_closureInterior (X := X) (A := A) hP2 hA
  · intro hCl
    exact nonempty_of_closureInterior_nonempty (X := X) (A := A) hCl