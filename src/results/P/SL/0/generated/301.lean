

theorem P2_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P2 (closure (B : Set X)) →
      Topology.P2 (closure (A ∪ B : Set X)) := by
  intro hA hB
  -- Apply the union lemma to the two closures.
  have hUnion :
      Topology.P2 (closure (A : Set X) ∪ closure (B : Set X)) :=
    Topology.P2_union (X := X)
      (A := closure (A : Set X)) (B := closure (B : Set X)) hA hB
  -- Re‐express the union of closures as the closure of the union.
  simpa [closure_union] using hUnion