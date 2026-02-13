

theorem P2_univ_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    {B : Set Y} (hB : B.Nonempty) :
    Topology.P2 ((Set.univ : Set X) ×ˢ B) ↔ Topology.P2 B := by
  -- A witness that `Set.univ : Set X` is nonempty.
  have hA : (Set.univ : Set X).Nonempty := Set.nonempty_univ
  -- General equivalence for products.
  have hEquiv :=
    (Topology.P2_prod_iff
        (A := (Set.univ : Set X)) (B := B) hA hB)
  -- `P2` holds for the whole space.
  have hP2_univ : Topology.P2 (Set.univ : Set X) :=
    Topology.P2_univ (X := X)
  constructor
  · intro hProd
    -- Extract the second component from the equivalence.
    exact (hEquiv.mp hProd).2
  · intro hPB
    -- Combine with the universal set's `P2` to apply the equivalence.
    exact hEquiv.mpr ⟨hP2_univ, hPB⟩