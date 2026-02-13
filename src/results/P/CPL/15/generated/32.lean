

theorem P3_closed_iff_eq_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : (P3 A) ↔ interior (closure A) = A := by
  -- Since `A` is closed, its closure is itself.
  have hcl : closure (A : Set X) = A := hA.closure_eq
  -- `P3 A` is equivalent to `P2 A` for closed sets.
  have hP3_P2 : (P3 A) ↔ (P2 A) :=
    (P2_iff_P3_of_closed (A := A) hA).symm
  -- For a closed set, `P2 A` is equivalent to `interior A = A`.
  have hP2_int : (P2 A) ↔ interior A = A :=
    P2_closed_iff_interior_eq (A := A) hA
  -- Combine the two equivalences.
  have hP3_int : (P3 A) ↔ interior A = A :=
    hP3_P2.trans hP2_int
  -- Rewrite using `hcl` to obtain the required statement.
  simpa [hcl] using hP3_int

theorem P3_iff_P2_of_dense_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h_dense : closure (interior A) = closure A) : P3 A ↔ P2 A := by
  have h_int : interior (closure (interior A)) = interior (closure A) := by
    simpa [h_dense]
  constructor
  · intro hP3
    intro x hx
    have hx_int : x ∈ interior (closure A) := hP3 hx
    simpa [h_int] using hx_int
  · intro hP2
    exact P2_subset_P3 (A := A) hP2