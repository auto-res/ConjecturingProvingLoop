

theorem closure_inter_closure_compl_eq_closure_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∩ closure (Aᶜ) = closure A \ interior A := by
  classical
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxClA, hxClAc⟩
    have hEq : closure (Aᶜ) = (interior A)ᶜ :=
      closure_compl_eq_compl_interior (α := X) (s := A)
    have hNotIntA : x ∉ interior A := by
      have : x ∈ (interior A)ᶜ := by
        simpa [hEq] using hxClAc
      simpa using this
    exact And.intro hxClA hNotIntA
  · intro hx
    rcases hx with ⟨hxClA, hNotIntA⟩
    have hEq : closure (Aᶜ) = (interior A)ᶜ :=
      closure_compl_eq_compl_interior (α := X) (s := A)
    have hxClAc : x ∈ closure (Aᶜ) := by
      have : x ∈ (interior A)ᶜ := hNotIntA
      simpa [hEq] using this
    exact And.intro hxClA hxClAc