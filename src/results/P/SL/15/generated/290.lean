

theorem P1_closure_prod_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hAne : A.Nonempty) (hBne : B.Nonempty) :
    Topology.P1 (closure A ×ˢ closure B) ↔
      (Topology.P1 (closure A) ∧ Topology.P1 (closure B)) := by
  -- The closures of non-empty sets are themselves non-empty.
  have hAneCl : (closure (A : Set X)).Nonempty := by
    rcases hAne with ⟨a, ha⟩
    exact ⟨a, subset_closure ha⟩
  have hBneCl : (closure (B : Set Y)).Nonempty := by
    rcases hBne with ⟨b, hb⟩
    exact ⟨b, subset_closure hb⟩
  -- Use the existing equivalence for products and transport it to closures.
  constructor
  · intro hProd
    exact
      (Topology.P1_prod_implies_P1_left_and_right
          (X := X) (Y := Y)
          (A := closure A) (B := closure B)
          hProd hAneCl hBneCl)
  · rintro ⟨hPA, hPB⟩
    exact
      Topology.P1_prod
        (X := X) (Y := Y)
        (A := closure A) (B := closure B) hPA hPB