

theorem Topology.interior_iUnion_of_isOpen {X : Type*} [TopologicalSpace X] {ι : Type*}
    {s : ι → Set X} :
    (∀ i, IsOpen (s i)) →
      interior (⋃ i, s i : Set X) = ⋃ i, interior (s i) := by
  intro hOpen
  -- The union of the open sets is open.
  have hOpenUnion : IsOpen (⋃ i, s i : Set X) :=
    isOpen_iUnion (fun i => hOpen i)
  -- Hence its interior is itself.
  have h₁ : interior (⋃ i, s i : Set X) = (⋃ i, s i : Set X) :=
    hOpenUnion.interior_eq
  -- Rewrite each `s i` by `interior (s i)` (they coincide because `s i` is open).
  have h₂ : (⋃ i, s i : Set X) = ⋃ i, interior (s i) := by
    classical
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
      have : x ∈ interior (s i) := by
        simpa [(hOpen i).interior_eq] using hx_i
      exact Set.mem_iUnion.2 ⟨i, this⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
      have : x ∈ s i :=
        (interior_subset : interior (s i) ⊆ s i) hx_i
      exact Set.mem_iUnion.2 ⟨i, this⟩
  simpa [h₂] using h₁