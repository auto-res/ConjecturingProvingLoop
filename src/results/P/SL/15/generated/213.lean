

theorem P1_closure_prod
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    Topology.P1 A → Topology.P1 B →
      Topology.P1 (closure A ×ˢ closure B) := by
  intro hA hB
  -- First, upgrade the hypotheses to the closures of the factors.
  have hAc : Topology.P1 (closure A) :=
    Topology.P1_implies_P1_closure (X := X) (A := A) hA
  have hBc : Topology.P1 (closure B) :=
    Topology.P1_implies_P1_closure (X := Y) (A := B) hB
  -- Apply the product rule for `P1`.
  simpa using
    (Topology.P1_prod
        (X := X) (Y := Y)
        (A := closure A) (B := closure B) hAc hBc)