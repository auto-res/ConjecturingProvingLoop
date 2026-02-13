

theorem P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (closure A ∪ closure B) := by
  intro hP1A hP1B
  -- First, upgrade `P1` for `A` and `B` to their closures.
  have hP1ClosA : Topology.P1 (closure A) :=
    Topology.P1_closure (A := A) hP1A
  have hP1ClosB : Topology.P1 (closure B) :=
    Topology.P1_closure (A := B) hP1B
  -- Apply the union lemma to the two closures.
  exact Topology.P1_union hP1ClosA hP1ClosB