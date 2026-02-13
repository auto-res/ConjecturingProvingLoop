

theorem P2_prod_univ_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} [Nonempty Y] (hA : A.Nonempty) :
    Topology.P2 (A ×ˢ (Set.univ : Set Y)) ↔ Topology.P2 A := by
  -- `Set.univ : Set Y` is nonempty under the given typeclass assumption.
  have hB : (Set.univ : Set Y).Nonempty := Set.nonempty_univ
  -- Invoke the general product equivalence for `P2`.
  have hEquiv :=
    (Topology.P2_prod_iff (A := A) (B := (Set.univ : Set Y)) hA hB)
  -- Use the fact that `P2` holds for `Set.univ`.
  have hP2_univ : Topology.P2 (Set.univ : Set Y) :=
    Topology.P2_univ (X := Y)
  -- Split the equivalence into the desired two implications.
  constructor
  · intro hProd
    exact (hEquiv.mp hProd).1
  · intro hPA
    exact hEquiv.mpr ⟨hPA, hP2_univ⟩