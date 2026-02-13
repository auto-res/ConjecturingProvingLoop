

theorem closure_interior_eq_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → closure (interior A) = closure A := by
  intro hP1
  apply Set.Subset.antisymm
  · exact closure_mono interior_subset
  ·
    have hsubset : (A : Set X) ⊆ closure (interior A) := hP1
    have hclosure : closure A ⊆ closure (closure (interior A)) := closure_mono hsubset
    simpa [closure_closure] using hclosure

theorem P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P2 A := by
  refine ⟨?fwd, ?rev⟩
  · intro _hP1
    intro x hx
    have hx_int : x ∈ interior (closure A) :=
      (interior_maximal subset_closure hA) hx
    simpa [hA.interior_eq] using hx_int
  · intro hP2
    exact P2_to_P1 (A := A) hP2