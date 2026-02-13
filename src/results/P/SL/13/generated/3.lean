

theorem isOpen_subset_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 (X:=X) A := by
  dsimp [Topology.P3]
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  have h_incl : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact h_incl hx_int