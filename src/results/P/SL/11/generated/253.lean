

theorem P123_prod_univ_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty Y] {A : Set X} (hA : A.Nonempty) :
    (Topology.P1 (A ×ˢ (Set.univ : Set Y)) ∧
      Topology.P2 (A ×ˢ (Set.univ : Set Y)) ∧
      Topology.P3 (A ×ˢ (Set.univ : Set Y))) ↔
      (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) := by
  -- A witness that `Set.univ : Set Y` is nonempty.
  have hB : (Set.univ : Set Y).Nonempty := Set.nonempty_univ
  -- General equivalence for products.
  have hEquiv :=
    (Topology.P123_prod_iff (A := A) (B := (Set.univ : Set Y)) hA hB)
  -- The triple of properties holds for the whole space.
  have hTripleUniv :
      Topology.P1 (Set.univ : Set Y) ∧
        Topology.P2 (Set.univ : Set Y) ∧
        Topology.P3 (Set.univ : Set Y) :=
    Topology.P123_univ (X := Y)
  constructor
  · intro hProd
    -- Extract the factor corresponding to `A`.
    exact (hEquiv.mp hProd).1
  · intro hTripleA
    -- Combine the triple for `A` with that for `univ` and reassemble.
    have hPair :
        (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) ∧
          (Topology.P1 (Set.univ : Set Y) ∧
            Topology.P2 (Set.univ : Set Y) ∧
            Topology.P3 (Set.univ : Set Y)) :=
      ⟨hTripleA, hTripleUniv⟩
    exact hEquiv.mpr hPair