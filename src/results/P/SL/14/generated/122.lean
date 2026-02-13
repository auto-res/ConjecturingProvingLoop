

theorem Topology.P3_union_isOpen_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 A) (hB : IsOpen B) :
    Topology.P3 (A ∪ B) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      -- Case `x ∈ A`
      have hxA_int : (x : X) ∈ interior (closure A) := hA hxA
      have h_closure_mono : closure A ⊆ closure (A ∪ B) := by
        have : (A : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact closure_mono this
      have h_int_mono :
          interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_closure_mono
      exact h_int_mono hxA_int
  | inr hxB =>
      -- Case `x ∈ B`
      have h_subset : (B : Set X) ⊆ interior (closure B) :=
        interior_maximal (subset_closure : (B : Set X) ⊆ closure B) hB
      have hxB_int : (x : X) ∈ interior (closure B) := h_subset hxB
      have h_closure_mono : closure B ⊆ closure (A ∪ B) := by
        have : (B : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact closure_mono this
      have h_int_mono :
          interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_closure_mono
      exact h_int_mono hxB_int