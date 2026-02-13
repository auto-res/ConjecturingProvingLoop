

theorem P1_nonempty_iff_closureInterior_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) :
    A.Nonempty ↔ (closure (interior A)).Nonempty := by
  constructor
  · intro hA
    exact
      Topology.P1_nonempty_closureInterior (X := X) (A := A) hP1 hA
  · intro hCl
    exact
      nonempty_of_closureInterior_nonempty (X := X) (A := A) hCl