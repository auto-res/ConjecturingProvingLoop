

theorem Topology.interior_eq_closure_iff_isClopen {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) = closure A ↔ (IsClosed A ∧ IsOpen A) := by
  constructor
  · intro hEq
    -- First, deduce `A = interior A`.
    have hA_sub_int : (A : Set X) ⊆ interior A := by
      have hA_sub_cl : (A : Set X) ⊆ closure A := subset_closure
      simpa [hEq] using hA_sub_cl
    have h_int_eq : interior A = (A : Set X) :=
      subset_antisymm interior_subset hA_sub_int
    -- Next, deduce `A = closure A`.
    have h_cl_eq : closure A = (A : Set X) := by
      calc
        closure A = interior A := by
          symm; simpa using hEq
        _ = A := by
          simpa using h_int_eq
    -- Conclude that `A` is both closed and open.
    have hOpen : IsOpen (A : Set X) := by
      simpa [h_int_eq] using (isOpen_interior : IsOpen (interior A))
    have hClosed : IsClosed (A : Set X) := by
      simpa [h_cl_eq] using (isClosed_closure : IsClosed (closure A))
    exact ⟨hClosed, hOpen⟩
  · rintro ⟨hClosed, hOpen⟩
    -- From clopeness, both interior and closure equal `A`.
    have h_int : interior (A : Set X) = A := hOpen.interior_eq
    have h_cl  : closure (A : Set X) = A := hClosed.closure_eq
    simpa [h_int, h_cl]