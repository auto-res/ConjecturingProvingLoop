

theorem Topology.P1_union_closure {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B →
      Topology.P1 (closure (A : Set X) ∪ closure (B : Set X)) := by
  intro hP1A hP1B
  -- First, upgrade `P1 A` and `P1 B` to their closures.
  have hP1_clA : Topology.P1 (closure (A : Set X)) :=
    Topology.P1_closure_of_P1 (A := A) hP1A
  have hP1_clB : Topology.P1 (closure (B : Set X)) :=
    Topology.P1_closure_of_P1 (A := B) hP1B
  -- Apply the union lemma for `P1`.
  have hUnion :=
    Topology.P1_union (A := closure (A : Set X)) (B := closure (B : Set X))
      hP1_clA hP1_clB
  -- Rewrite the goal in a convenient form.
  simpa using hUnion