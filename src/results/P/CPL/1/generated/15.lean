

theorem P1_and_P3_iff_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : (P1 A ∧ P3 A) ↔ P2 A := by
  constructor
  · rintro ⟨hP1, hP3⟩
    intro x hx
    -- `x` is in the interior of `closure A` by `P3`.
    have hx_int_closureA : x ∈ interior (closure A) := hP3 hx
    -- From `P1` we have equality of the two closures.
    have h_closure_eq : closure (interior A) = closure A :=
      closure_interior_eq_of_P1 (A := A) hP1
    -- Rewrite to obtain the desired membership.
    simpa [h_closure_eq] using hx_int_closureA
  · intro hP2
    exact ⟨P1_of_P2 (A := A) hP2, P3_of_P2 (A := A) hP2⟩

theorem P2_iff_nhds {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A ↔ ∀ x ∈ A, interior (closure (interior A)) ∈ 𝓝 x := by
  refine ⟨?forward, ?backward⟩
  · intro hP2 x hx
    have hx_int : x ∈ interior (closure (interior A)) := hP2 hx
    exact (isOpen_interior).mem_nhds hx_int
  · intro h x hx
    have h_mem : interior (closure (interior A)) ∈ 𝓝 x := h x hx
    exact mem_of_mem_nhds h_mem