

theorem P1_sUnion_union {X : Type*} [TopologicalSpace X] {𝒜 𝓑 : Set (Set X)} (hA : ∀ A ∈ 𝒜, P1 A) (hB : ∀ B ∈ 𝓑, P1 B) : P1 (⋃₀ (𝒜 ∪ 𝓑)) := by
  -- First, prove that every set belonging to `𝒜 ∪ 𝓑` satisfies `P1`.
  have h_union : ∀ S : Set X, S ∈ (𝒜 ∪ 𝓑 : Set (Set X)) → P1 S := by
    intro S hS
    cases hS with
    | inl hS𝒜 => exact hA S hS𝒜
    | inr hS𝓑 => exact hB S hS𝓑
  -- Apply `P1_sUnion` to the union family.
  simpa using
    (P1_sUnion (X := X) (𝒜 := (𝒜 ∪ 𝓑)) h_union)

theorem P3_Unionᵢ_closed {X : Type*} [TopologicalSpace X] {ι : Type*} {A : ι → Set X} (hA : ∀ i, IsClosed (A i) ∧ P3 (A i)) : P3 (⋃ i, A i) := by
  simpa using P3_Unionᵢ (A := A) (fun i => (hA i).2)