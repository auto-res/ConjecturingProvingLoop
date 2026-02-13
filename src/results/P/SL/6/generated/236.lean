

theorem sUnion_open_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → IsOpen (A : Set X)) :
    Topology.P1 (⋃₀ 𝒜 : Set X) ∧ Topology.P2 (⋃₀ 𝒜) ∧ Topology.P3 (⋃₀ 𝒜) := by
  classical
  -- First, show that the `sUnion` is an open set.
  have hOpen : IsOpen (⋃₀ 𝒜 : Set X) := by
    -- Re-express `⋃₀ 𝒜` as an `iUnion` over a subtype and apply `isOpen_iUnion`.
    simpa [Set.sUnion_eq_iUnion] using
      isOpen_iUnion (fun A : {B : Set X // B ∈ 𝒜} =>
        h𝒜 A A.property)
  -- Open sets satisfy all three properties simultaneously.
  simpa using
    Topology.open_satisfies_all_Ps (A := ⋃₀ 𝒜) hOpen