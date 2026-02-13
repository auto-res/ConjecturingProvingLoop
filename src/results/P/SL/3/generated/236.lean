

theorem P2_union_interiors {X : Type*} [TopologicalSpace X] (A B : Set X) :
    Topology.P2 (interior (A : Set X) ∪ interior (B : Set X)) := by
  have hA : Topology.P2 (interior (A : Set X)) :=
    P2_interior (A := A)
  have hB : Topology.P2 (interior (B : Set X)) :=
    P2_interior (A := B)
  simpa using
    (P2_union
      (A := interior (A : Set X))
      (B := interior (B : Set X))
      hA hB)