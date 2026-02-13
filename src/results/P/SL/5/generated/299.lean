

theorem closureInterior_inter_interiorClosure_nonempty_of_P1_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) (hP3 : Topology.P3 (X := X) A)
    (hA : (A : Set X).Nonempty) :
    (closure (interior A) ∩ interior (closure (A : Set X))).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  have hx₁ : x ∈ closure (interior A) := hP1 hxA
  have hx₂ : x ∈ interior (closure (A : Set X)) := hP3 hxA
  exact ⟨x, ⟨hx₁, hx₂⟩⟩