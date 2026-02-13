

theorem P1_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → closure A = Set.univ → P1 A := by
  intro hClosed hDense
  -- Since `A` is closed, `closure A = A`.
  have hA_closure : closure A = A := hClosed.closure_eq
  -- Hence `A = univ`.
  have hA_univ : (A : Set X) = Set.univ := by
    calc
      A = closure A := (hA_closure).symm
      _ = Set.univ := hDense
  -- Establish the `P1` property.
  intro x hxA
  -- Interpret `hxA` as membership in `univ`.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    simpa [hA_univ] using hxA
  -- Rewrite the goal using `A = univ`.
  simpa [hA_univ, interior_univ, closure_univ] using hx_univ