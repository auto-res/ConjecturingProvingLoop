

theorem P3_prod_univ_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} [Nonempty Y] (hA : A.Nonempty) :
    Topology.P3 (A ×ˢ (Set.univ : Set Y)) ↔ Topology.P3 A := by
  -- A witness that `Set.univ : Set Y` is nonempty.
  have hB : (Set.univ : Set Y).Nonempty := Set.nonempty_univ
  -- Use the general product equivalence for `P3`.
  have hEquiv :=
    (Topology.P3_prod_iff (A := A) (B := (Set.univ : Set Y)) hA hB)
  -- `P3` holds trivially for the whole space.
  have hP3_univ : Topology.P3 (Set.univ : Set Y) := Topology.P3_univ
  constructor
  · intro hProd
    exact (hEquiv.mp hProd).1
  · intro hPA
    exact hEquiv.mpr ⟨hPA, hP3_univ⟩