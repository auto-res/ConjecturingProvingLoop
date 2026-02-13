

theorem P1_univ_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] {B : Set Y} (hB : B.Nonempty) :
    Topology.P1 ((Set.univ : Set X) ×ˢ B) ↔ Topology.P1 B := by
  -- A witness that `Set.univ : Set X` is nonempty.
  have hA : (Set.univ : Set X).Nonempty := Set.nonempty_univ
  -- Apply the existing product equivalence for `P1`.
  have hEquiv :=
    (Topology.P1_prod_iff (A := (Set.univ : Set X)) (B := B) hA hB)
  -- `P1` holds for the universal set.
  have hP1_univ : Topology.P1 (Set.univ : Set X) := Topology.P1_univ (X := X)
  -- Split the equivalence into the desired two implications.
  constructor
  · intro hProd
    exact (hEquiv.mp hProd).2
  · intro hPB
    exact hEquiv.mpr ⟨hP1_univ, hPB⟩