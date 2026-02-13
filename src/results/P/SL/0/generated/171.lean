

theorem sUnion_open_has_all_Ps {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → IsOpen (A : Set X)) :
    Topology.P1 (⋃₀ 𝒜) ∧ Topology.P2 (⋃₀ 𝒜) ∧ Topology.P3 (⋃₀ 𝒜) := by
  -- The union of an arbitrary family of open sets is open.
  have hOpen : IsOpen (⋃₀ 𝒜 : Set X) := isOpen_sUnion h𝒜
  -- Every open set satisfies `P1`, `P2`, and `P3`.
  simpa using
    (Topology.isOpen_has_all_Ps (X := X) (A := (⋃₀ 𝒜 : Set X)) hOpen)