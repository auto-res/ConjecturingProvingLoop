

theorem P2_closure_prod_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    Topology.P2 (closure A ×ˢ closure B) ↔
      (Topology.P2 (closure A) ∧ Topology.P2 (closure B)) := by
  -- Closures of nonempty sets are nonempty.
  have hAneClosure : (closure (A : Set X)).Nonempty := by
    rcases hAne with ⟨x, hx⟩
    exact ⟨x, subset_closure hx⟩
  have hBneClosure : (closure (B : Set Y)).Nonempty := by
    rcases hBne with ⟨y, hy⟩
    exact ⟨y, subset_closure hy⟩
  -- Apply the existing equivalence for products.
  simpa using
    (Topology.P2_prod_iff
        (X := X) (Y := Y)
        (A := closure A) (B := closure B)
        hAneClosure hBneClosure)