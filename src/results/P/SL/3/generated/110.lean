

theorem openInterInterior_subset_and_open {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) :
    (A ∩ interior (B : Set X) : Set X) ⊆ A ∩ B ∧
      IsOpen (A ∩ interior (B : Set X)) := by
  refine And.intro ?_ ?_
  · -- Subset part
    intro x hx
    rcases hx with ⟨hAx, hIntBx⟩
    have hBx : (x : X) ∈ (B : Set X) :=
      interior_subset (s := B) hIntBx
    exact And.intro hAx hBx
  · -- Openness part
    exact hA.inter isOpen_interior