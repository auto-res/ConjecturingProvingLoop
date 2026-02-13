

theorem P1_prod_univ_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} [Nonempty Y] (hA : A.Nonempty) :
    Topology.P1 (A ×ˢ (Set.univ : Set Y)) ↔ Topology.P1 A := by
  -- A witness for the nonemptiness of `Set.univ : Set Y`.
  have hB : (Set.univ : Set Y).Nonempty := Set.nonempty_univ
  -- Use the existing equivalence for products.
  have hEquiv :=
    (Topology.P1_prod_iff (A := A) (B := (Set.univ : Set Y)) hA hB)
  -- `P1` holds for the universal set.
  have hP1_univ : Topology.P1 (Set.univ : Set Y) := Topology.P1_univ
  constructor
  · intro hProd
    -- Extract `P1 A` from the equivalence.
    exact (hEquiv.mp hProd).1
  · intro hP1A
    -- Re-assemble the pair to use the equivalence in the other direction.
    exact hEquiv.mpr ⟨hP1A, hP1_univ⟩