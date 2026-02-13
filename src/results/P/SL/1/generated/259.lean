

theorem Topology.P2_closure_union_iff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 (closure (A ∪ B)) ↔ Topology.P2 (closure A ∪ closure B) := by
  have h : closure (A ∪ B : Set X) = closure A ∪ closure B := by
    simpa [closure_union]
  constructor
  · intro hP2
    simpa [h] using hP2
  · intro hP2
    simpa [h] using hP2