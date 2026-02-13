

theorem P1_union_interior {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 (A ∪ interior B) := by
  intro hP1A
  -- `interior B` automatically satisfies `P1`.
  have hP1IntB : Topology.P1 (interior B) :=
    Topology.P1_interior (X := X) (A := B)
  -- Combine the two `P1` sets using the existing union lemma.
  exact
    (Topology.P1_union (A := A) (B := interior B) hP1A hP1IntB)