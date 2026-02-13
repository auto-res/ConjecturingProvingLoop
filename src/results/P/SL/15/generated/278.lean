

theorem P3_closure_prod_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hAne : A.Nonempty) (hBne : B.Nonempty) :
    Topology.P3 (closure A ×ˢ closure B) ↔
      (Topology.P3 (closure A) ∧ Topology.P3 (closure B)) := by
  -- Non‐emptiness of the closures follows from the non‐emptiness of the sets.
  have hAneClosure : (closure (A : Set X)).Nonempty := by
    rcases hAne with ⟨x, hx⟩
    exact ⟨x, subset_closure hx⟩
  have hBneClosure : (closure (B : Set Y)).Nonempty := by
    rcases hBne with ⟨y, hy⟩
    exact ⟨y, subset_closure hy⟩
  -- Apply the existing equivalence for products.
  simpa using
    (Topology.P3_prod_iff
        (X := X) (Y := Y)
        (A := closure A) (B := closure B)
        hAneClosure hBneClosure)