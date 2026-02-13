

theorem P1_prod_univ_left {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : Topology.P1 A → Topology.P1 (A ×ˢ (Set.univ : Set Y)) := by
  intro hP1A
  -- `univ` in `Y` trivially satisfies `P1`.
  have hP1_univ : P1 (Set.univ : Set Y) := by
    simpa using (P1_univ (X := Y))
  -- Apply the product lemma.
  simpa using
    (P1_prod (A := A) (B := (Set.univ : Set Y)) hP1A hP1_univ)