

theorem P3_univ_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] {B : Set Y} (hB : B.Nonempty) :
    Topology.P3 ((Set.univ : Set X) ×ˢ B) ↔ Topology.P3 B := by
  -- `Set.univ : Set X` is nonempty by assumption.
  have hA : (Set.univ : Set X).Nonempty := Set.nonempty_univ
  -- Apply the general product equivalence for `P3`.
  have hEquiv :=
    (Topology.P3_prod_iff
        (A := (Set.univ : Set X)) (B := B) hA hB)
  -- `P3` holds trivially for the universal set.
  have hP3_univ : Topology.P3 (Set.univ : Set X) := Topology.P3_univ
  constructor
  · intro hProd
    -- Extract the factor corresponding to `B`.
    exact (hEquiv.mp hProd).2
  · intro hPB
    -- Combine with the universal factor and reassemble via the equivalence.
    exact hEquiv.mpr ⟨hP3_univ, hPB⟩