

theorem P123_univ_prod_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    {B : Set Y} (hB : B.Nonempty) :
    (Topology.P1 ((Set.univ : Set X) ×ˢ B) ∧
      Topology.P2 ((Set.univ : Set X) ×ˢ B) ∧
      Topology.P3 ((Set.univ : Set X) ×ˢ B)) ↔
      (Topology.P1 B ∧ Topology.P2 B ∧ Topology.P3 B) := by
  -- `Set.univ : Set X` is nonempty by assumption.
  have hA : (Set.univ : Set X).Nonempty := Set.nonempty_univ
  -- Use the general product equivalence for the triple of properties.
  have hEquiv :=
    (Topology.P123_prod_iff
        (A := (Set.univ : Set X)) (B := B) hA hB)
  -- The triple of properties holds for the universal set.
  have hTripleUniv :
      Topology.P1 (Set.univ : Set X) ∧
        Topology.P2 (Set.univ : Set X) ∧
        Topology.P3 (Set.univ : Set X) :=
    Topology.P123_univ (X := X)
  constructor
  · intro hProd
    -- Extract the triple for `B` from the equivalence.
    exact (hEquiv.mp hProd).2
  · intro hTripleB
    -- Combine the triple for `B` with the one for `univ`
    -- and reassemble via the equivalence.
    exact
      hEquiv.mpr ⟨hTripleUniv, hTripleB⟩