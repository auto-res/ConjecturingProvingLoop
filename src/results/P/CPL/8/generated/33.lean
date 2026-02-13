

theorem P3_iff_P2_of_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = closure (interior A) → (P3 A ↔ P2 A) := by
  intro hEq
  refine ⟨?forward, ?backward⟩
  · intro hP3
    intro x hxA
    have hx_int : x ∈ interior (closure A) := hP3 hxA
    simpa [hEq] using hx_int
  · intro hP2
    exact P2_to_P3 (A := A) hP2