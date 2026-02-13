

theorem P3_union_interiors {X : Type*} [TopologicalSpace X] (A B : Set X) :
    Topology.P3 (interior (A : Set X) ∪ interior B) := by
  have hA : Topology.P3 (interior (A : Set X)) := P3_interior (A := A)
  have hB : Topology.P3 (interior (B : Set X)) := P3_interior (A := B)
  simpa using
    (P3_union
      (A := interior (A : Set X))
      (B := interior (B : Set X))
      hA hB)