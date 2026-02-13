

theorem Topology.interior_diff_closed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsClosed B) :
    interior (A \ B) = interior A \ B := by
  ext x
  constructor
  · intro hx
    have hxA : x ∈ interior A := by
      -- `A \ B ⊆ A`, hence `interior (A \ B) ⊆ interior A`.
      have h_subset : (A \ B : Set X) ⊆ A := fun y hy => hy.1
      exact (interior_mono h_subset) hx
    have hxNotB : x ∉ B := by
      -- Points in `interior (A \ B)` are certainly not in `B`.
      have hxAB : x ∈ A \ B := interior_subset hx
      exact hxAB.2
    exact And.intro hxA hxNotB
  · intro hx
    rcases hx with ⟨hxIntA, hxNotB⟩
    -- Construct an open neighborhood contained in `A \ B`.
    have hOpenIntA : IsOpen (interior A) := isOpen_interior
    have hOpenComplB : IsOpen (Bᶜ) := hB.isOpen_compl
    have hVopen : IsOpen (interior A ∩ Bᶜ) := hOpenIntA.inter hOpenComplB
    have hxV : x ∈ interior A ∩ Bᶜ := And.intro hxIntA hxNotB
    -- This neighborhood is included in `A \ B`.
    have hVsubset : (interior A ∩ Bᶜ) ⊆ (A \ B) := by
      intro y hy
      have hyA : y ∈ A := interior_subset hy.1
      exact And.intro hyA hy.2
    -- Hence `x` lies in `interior (A \ B)`.
    have hVsubsetInterior : (interior A ∩ Bᶜ) ⊆ interior (A \ B) :=
      interior_maximal hVsubset hVopen
    exact hVsubsetInterior hxV